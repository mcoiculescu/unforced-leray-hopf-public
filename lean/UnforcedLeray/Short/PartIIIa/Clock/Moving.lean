import UnforcedLeray.Short.PartIIIa.FullClock
import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-a full clock: the moving-coordinate proof objects (SP 2855-3030)

Proof objects for `FullClockLongForward` (SP 2837-2845, 2861-3030), all stated over the ACTUAL
train `tr` and the weak linearised flows `IsLinearisedFlow` of `Defs.lean`:

* `movingZ`, `movingW`: the exact substitution `w(s,x) = a^{-2} W(z, x/√a)`, `z = s/a` (SP 2855-2866),
  i.e. `W(z(s)) = J_a⁻¹ w(s)` (`JscaleInv`), on the cell of length `d = c/√a` (`cellLen`).
* `MovingFrame`: the periodized growing vectors `E(z)` and dual rows `Λ(z)` with `Λ E = I₂`
  and uniform bounds (SP 2891-2897). Its construction from the planar seed of Part I is NOT in
  this file (Part I does not export the periodized `E(z)`, `Λ(z)`): that is the leaf
  `PartIII-a:T21/c1`.
* `FreeMovingEnergy` (SP 2937-2958, `eq:short-causal-free-moving`): the weighted energy bound for
  the free moving evolution (`IsFreeCylFlow`), norm-growth contribution `C_m = (m²+3m+3)/2`.
* `FrameStable`, `FrameAmplitude` (SP 2975-3004): the block-product stability
  `eq:short-causal-stable-moving` in its consumed form `‖r(z)‖ ≤ C e^{-h₀(z-t)}‖r(t)‖ + C η A_*`,
  and the integral form of the amplitude equation (diagonal `λ_i + κ_i/θ` removed by the
  normalisation by `N`, couplings `C(θ⁻¹ + δ_*)`).
* `AmplitudeGronwall` (SP 3005-3016): the scalar budget.
* `LongForwardEstimate`: the second conjunct of `FullClockLongForward`.

Every statement over the actual train `tr` assumes the BUC class `PartI.IsBUCTrain tr`
(`Short/PartI/TrainClass.lean`; the train of `sct:train`, SP 270-288): the proofs use the rescaled
train comparison (SP 2866-2871), the actual-base velocity errors `δ_ν` (SP 2954-2956), the direct
errors `δ_*` (SP 2992-2995) and, for existence, bounded coefficients (SP 2819-2836), none of which
follows from `B0140.IsTrain`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `z = s/a(s) = ν⁻¹ - θ` (SP 2855). -/
def movingZ (ν s : ℝ) : ℝ := s / clockA ν s

/-- The moving-coordinate solution `W(z(s)) = J_{a(s)}⁻¹ w(s)` (SP 2861). -/
def movingW (ν : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) : ℝ × ℝ → ℂ := JscaleInv (clockA ν s) (w s)

/-- The cell of the moving coordinate at age `s`: length `d = c/√a(s)`. -/
def movingCell (ν c s : ℝ) : Set (ℝ × ℝ) := B0579.cell (cellLen c (clockA ν s))

/-- `C_m = (m²+3m+3)/2` (SP 2954). -/
def normGrowthConst (m : ℝ) : ℝ := (m ^ 2 + 3 * m + 3) / 2

/-- Free weighted energy in moving coordinates (SP 2937-2958): for every `ε > 0`, `b` large and
`ν` small, for every actual train `tr` of the BUC class (SP 270-288; its velocity errors enter
`δ_ν`, SP 2954-2956), the free evolution `ω` (real data) satisfies
`‖J_{a_s}⁻¹ ω(s)‖_{X_{m,d_s}} ≤ exp{(C_m/b + ε)(z_s - z_t)} ‖J_{a_t}⁻¹ f‖_{X_{m,d_t}}`
for `b ≤ θ(s)` (this is `eq:short-causal-free-moving` with the gain `e^{-∫β₀}` removed,
`β₀ = γ + Re κ/θ ≤ γ + |Re κ|/b`). -/
def FreeMovingEnergy : Prop :=
  ∀ m : ℝ, 8 < m → ∀ ε : ℝ, 0 < ε → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
          ∀ ω : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t f ω →
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m
                (JscaleInv (clockA ν s) (fun x => ((ω s x : ℝ) : ℂ))) ≤
              ENNReal.ofReal (Real.exp ((normGrowthConst m / b + ε) * (movingZ ν s - movingZ ν t))) *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m
                  (JscaleInv (clockA ν t) (fun x => ((f x : ℝ) : ℂ)))

/-- The periodized growing vectors `E_i(s)` and normalised dual rows `Λ_i(s)` in the moving
coordinate (SP 2891-2897), `i ∈ Fin 2`: `Λ E = I₂` on the cell of length `d(s)` and uniform
bounds (`K`) in `X_{m,d}`; the `E_i` are smooth profiles (SP 2975-2991), recorded as a.e.
strong measurability on the cell (needed for the triangle inequality in `xNorm`). -/
structure MovingFrame (ν c m b K : ℝ) where
  E : ℝ → Fin 2 → ℝ × ℝ → ℂ
  lam : ℝ → Fin 2 → ℝ × ℝ → ℂ
  dual : ∀ s, 0 ≤ s → b ≤ clockTheta ν s → ∀ i j : Fin 2,
    ∫ x in movingCell ν c s, lam s i x * E s j x = if i = j then 1 else 0
  E_meas : ∀ s, 0 ≤ s → b ≤ clockTheta ν s → ∀ i,
    AEStronglyMeasurable (E s i) (volume.restrict (movingCell ν c s))
  E_bdd : ∀ s, 0 ≤ s → b ≤ clockTheta ν s → ∀ i, xNorm (cellLen c (clockA ν s)) m (E s i) ≤ ENNReal.ofReal K
  lam_bdd : ∀ s, 0 ≤ s → b ≤ clockTheta ν s → ∀ i (W : ℝ × ℝ → ℂ),
    ENNReal.ofReal ‖∫ x in movingCell ν c s, lam s i x * W x‖ ≤
      ENNReal.ofReal K * xNorm (cellLen c (clockA ν s)) m W

/-- The amplitudes `α_i(s) = Λ_i W(z(s))`. -/
def ampl {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) (i : Fin 2) : ℂ :=
  ∫ x in movingCell ν c s, F.lam s i x * movingW ν w s x

/-- `Σ_i |α_i(s)|`. -/
def amplNorm {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal ‖ampl F w s i‖

/-- The complement `r = W - Σ E_i α_i`, `Λ r = 0` (SP 2991). -/
def compl {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) :
    ℝ × ℝ → ℂ :=
  fun x => movingW ν w s x - ∑ i, ampl F w s i * F.E s i x

/-- The normaliser `e^{Re λ (θ_t-θ_s)} (θ_t/θ_s)^{Re κ}` of the amplitudes and the complement
(SP 2998-2999: the two conjugate modes have the same modulus). -/
def clockN (P : PlanarData) (ν t s : ℝ) : ℝ :=
  Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν s)) *
    (clockTheta ν t / clockTheta ν s) ^ P.kappa.re

/-- **Stable convolution** (SP 2975-3004, `eq:short-causal-stable-moving` in its consumed form):
`‖r(s)‖ ≤ N (C e^{-h₀(z_s-z_t)} ‖r(t)‖ + C η(s) A_*(s))`, `η = C(1+ν³)/θ`,
`A_*(s) = sup_{t≤u≤s} Σ|α_i(u)|/N(u)` (running maximum of the normalised amplitude); with the
a.e.-measurability of the two normalised quantities needed for the Gronwall step. For every actual
train of the BUC class (SP 270-288). -/
def FrameStable (P : PlanarData) {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (C h₀ : ℝ) : Prop :=
  ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s → ∀ f w u,
      IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u → HasZeroCirculation (ν ^ (-2 : ℝ)) f →
      AEMeasurable (fun r => amplNorm F w r / ENNReal.ofReal (clockN P ν t r))
        (volume.restrict (Icc t s)) ∧
      AEMeasurable (fun r => xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
        ENNReal.ofReal (clockN P ν t r)) (volume.restrict (Icc t s)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) ≤
        ENNReal.ofReal (clockN P ν t s) *
          (ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν s - movingZ ν t))) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t) +
            ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν s)) *
              ⨆ r ∈ Icc t s, amplNorm F w r / ENNReal.ofReal (clockN P ν t r))

/-- **Amplitude equation, integral form** (SP 2991-3000): with the diagonal `λ_i + κ_i/θ` removed
by `N`, direct error `δ = Cν³/θ` and coupling `C(θ⁻¹ + δ)`,
`Σ|α(s)|/N(s) ≤ Σ|α(t)| + ∫_t^s a(u)⁻² [δ Σ|α|/N + C(θ⁻¹+δ) ‖r‖/N] du`
(`dz = du/a²`). For every actual train of the BUC class (SP 270-288; the direct errors `δ_*`
come from the train comparison, SP 2992-2995). -/
def FrameAmplitude (P : PlanarData) {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (C : ℝ) : Prop :=
  ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s → ∀ f w u,
      IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u → HasZeroCirculation (ν ^ (-2 : ℝ)) f →
      amplNorm F w s / ENNReal.ofReal (clockN P ν t s) ≤ amplNorm F w t +
        ∫⁻ r in Ioc t s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) *
              (amplNorm F w r / ENNReal.ofReal (clockN P ν t r)) +
            ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
              (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
                ENNReal.ofReal (clockN P ν t r)))

/-- A good moving frame exists (the leaf `PartIII-a:T21/c1`, built from the Part I seed; its
`FrameStable` is `T21/c3` and its `FrameAmplitude` is `T21/c5`). -/
def GoodFrameExists : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ (K C h₀ b₀ : ℝ), 0 < h₀ ∧
    ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∃ F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K, FrameStable P F C h₀ ∧ FrameAmplitude P F C

/-- **The scalar budget** (SP 3005-3016, `∫_b^{1/ν}[δ_* + (r⁻¹+δ_*)²]dr` bounded). Normalised
amplitude `a` and complement `ρ` (functions of the age `r`), with the integral inequality of
`FrameAmplitude` and the stable convolution of `FrameStable`, satisfy
`a(s) + ρ(s) ≤ K_G (a(t) + ρ(t))` once `b` is large and `ν` small. The running maximum
`A_*(s) = ⨆_{t ≤ r ≤ s} a(r)` of the normalised amplitude (SP 3002-3004) is assumed finite: the
source amplitude is continuous in the age, hence locally bounded; pointwise finiteness of `a`
alone does not suffice (`Sub/T21_c4_old_refutation.lean`). -/
def AmplitudeGronwall : Prop :=
  ∀ C h₀ : ℝ, 0 < h₀ → 0 < C → ∃ (K_G b₀ : ℝ), ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
      ∀ a ρ : ℝ → ℝ≥0∞, (∀ r ∈ Icc t s, a r ≠ ⊤ ∧ ρ r ≠ ⊤) →
        AEMeasurable a (volume.restrict (Icc t s)) →
        AEMeasurable ρ (volume.restrict (Icc t s)) →
        (⨆ r ∈ Icc t s, a r) ≠ ⊤ →
        (∀ s' ∈ Icc t s, a s' ≤ a t +
          ∫⁻ r in Ioc t s', ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
            (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) * a r +
              ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) * ρ r)) →
        (∀ s' ∈ Icc t s, ρ s' ≤
          ENNReal.ofReal (C * Real.exp (-h₀ * (movingZ ν s' - movingZ ν t))) * ρ t +
            ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν s')) * ⨆ r ∈ Icc t s', a r) →
        a s + ρ s ≤ ENNReal.ofReal K_G * (a t + ρ t)

/-- The second conjunct of `FullClockLongForward` (SP 2837-2845), for every actual train of the BUC
class (SP 270-288). -/
def LongForwardEstimate : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
          ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (JscaleInv (clockA ν s) (w s)) ≤
                ENNReal.ofReal (C * Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν s)) *
                    (clockTheta ν t / clockTheta ν s) ^ P.kappa.re) *
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (JscaleInv (clockA ν t) f)

/-- Existence of the full evolution (first conjunct of `FullClockLongForward`), uniformly, for every
actual train of the BUC class (SP 270-288; the perturbation `B(t)` is bounded, SP 2819-2836). -/
def FullFlowExistsAll : Prop :=
  ∀ m : ℝ, 8 < m → ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr → FullFlowExists ν (ν ^ (-2 : ℝ)) m tr

/-- `FullClockLongForward` is existence plus the long estimate. -/
theorem fullClockLongForward_of (hEx : FullFlowExistsAll) (hL : LongForwardEstimate) :
    FullClockLongForward := by
  intro P hP m hm
  obtain ⟨b₀, hb₀⟩ := hL P hP m hm
  refine ⟨b₀, fun b hb => ?_⟩
  obtain ⟨C, ν₀, hν₀, h⟩ := hb₀ b hb
  refine ⟨C, ν₀, hν₀, fun ν hν tr htr => ⟨hEx m hm ν hν.1 tr htr, ?_⟩⟩
  intro t s ht hts hb' f hf hz w u hw
  exact h ν hν tr htr t s ht hts hb' f hf hz w u hw

end UnforcedLeray.Short.IIIa
