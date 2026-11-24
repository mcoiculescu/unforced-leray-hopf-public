import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1
import UnforcedLeray.Lib.EvolutionFamilies.Mild
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.ExpJoint
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative

/-!
# `PartI:C07/1/1/2`: decomposition of `CoupledImpliesFullMild`

Source `the November 2 reference manuscript`,
proof of Proposition `prop:short-canonical`, lines 1094-1125: `W = e^{λθ}θ^κ V = Aq + r`,
`r ∈ QX_G` (line 1095); the coupled equations `-A' = θ⁻¹ℓ(Dr)`,
`-r' = Q{L-λ+θ⁻¹(D-κ)}Qr + θ⁻¹A QDq` (lines 1097-1101); the forward complementary evolution
`S(θ,s)` (lines 1102-1104); the coupled mild initial-value equations obtained by "splitting both
integrals at any finite `s₀`" (lines 1117-1119).  `CoupledImpliesFullMild` says that these
coupled mild equations make `V = e^{-λθ}θ^{-κ}(Aq + r)` a mild solution of the full equation
`-V' = (L + θ⁻¹D)V` (`FullMildEq`).

Every intermediate statement is the backward Duhamel form `BwdMild` with respect to the free
evolution `E(θ,σ) = e^{(log σ - log θ)D}`, `b ≤ θ ≤ σ` (the evolution of `-X' = θ⁻¹DX`).

1. `complementFreeDuhamel` (proved here).  On every forward block `[-s₀,-b]` (`t = -θ`) the
   complementary evolution `U` of `IsMildComplementEvolution` (clock `canonicalClock b`, so
   `e^{D∫_r^tβ} = Cons.G3b.freeU t r` by `integral_canonicalClock`) is the Dyson evolution of
   `Cons.G3b.freeFam` perturbed by its bounded generator `B(t) = L - λ - P - β(t)κ + β(t)R_f`
   (`canonicalCplPert`, `cplMildIsDyson`, from `Evolution.dyson_unique`).  Variation of
   constants (`dyson_variation_mild`, from `Evolution.dyson_left` and `Evolution.dyson_inhom`)
   turns the `r`-equation `r(θ) = S(θ,s₀)r(s₀) + ∫_θ^{s₀} S(θ,s)QDq A(s)/s ds` into the free
   Duhamel form of `r` with coefficient `B(-σ)` and source `σ⁻¹A(σ)QDq`.
2. `AmplitudeFreeDuhamel` (**leaf**).  The integrated amplitude equation
   `A(θ) = A(s₀) + ∫_θ^{s₀} ℓ(Dr(s))/s ds` gives the free Duhamel form of `A q` (`q ∈ 𝒟(D)`)
   with source `σ⁻¹ℓ(Dr(σ))q - σ⁻¹A(σ)Dq`.
3. `canonicalGen_algebra` (proved here; the content of `seedRf_spec` on `ker ℓ`).  For `ℓr = 0`:
   `B(-σ)r + σ⁻¹A QDq + σ⁻¹ℓ(Dr)q - σ⁻¹A Dq = (L - λ - κ/σ)(r + Aq)`, by `Lq = λq`,
   `QDq = Dq - κq` and `R_f r = -ℓ(Dr)q`.  With `bwdMild_add` this is the free Duhamel form of
   `W` with the conjugated full coefficient `L - λ - κ/σ` (`canonicalFullGen`).
4. `BwdGauge` (**leaf**).  Undoing the normalization: `e^{-λθ}θ^{-κ}W` (`canonicalGauge`)
   solves the free Duhamel form with coefficient `L`; its hypothesis is the identity at every
   intermediate time supplied by `bwdMild_pullback` (proved here).
5. `canonicalGauge_smul_canonicalW`, `fullMildEq_of_bwdMild` (proved here): the gauge recovers
   `V`, and the change of variables `u = -σ` gives `FullMildEq`.

`coupledImpliesFullMild_of` assembles the two leaves.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

/-! ### The clock `β(t) = (max (-t) b)⁻¹` (lines 1102-1104) -/

theorem continuous_canonicalClock {b : ℝ} (hb : 0 < b) : Continuous (canonicalClock b) := by
  unfold canonicalClock
  exact (continuous_neg.max continuous_const).inv₀
    fun t => (lt_of_lt_of_le hb (le_max_right _ _)).ne'

/-- `∫_r^t β = log(-r) - log(-t)` for `r ≤ t ≤ -b`: the free part `e^{D∫_r^tβ}` of the
complementary evolution is `Cons.G3b.freeU t r = e^{(log θ_r - log θ_t)D}` (`θ = -t`). -/
theorem integral_canonicalClock {b r t : ℝ} (hb : 0 < b) (hrt : r ≤ t) (ht : t ≤ -b) :
    ∫ u in r..t, canonicalClock b u = Real.log (-r) - Real.log (-t) := by
  have h1 : ∫ u in r..t, canonicalClock b u = ∫ u in r..t, (-u)⁻¹ := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hrt] at hu
    exact canonicalClock_eq (hu.2.trans ht)
  have h2 := intervalIntegral.integral_comp_neg (a := r) (b := t) (f := fun u : ℝ => u⁻¹)
  rw [h1, h2, integral_inv_of_pos (by linarith) (by linarith),
    Real.log_div (by linarith) (by linarith)]

/-! ### The complementary generator as a bounded perturbation -/

/-- The generator of `IsMildComplementEvolution` for the canonical clock (lines 1014-1030,
1102-1104): `B(t) = L₀ - λ - P - β(t)κ + β(t)R_f`, `P = ℓ(·)q`, `β = canonicalClock b`. -/
def canonicalCplGen (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) (b t : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
    (canonicalClock b t * κ) • (1 : B0010.XG →L[ℂ] B0010.XG) + (canonicalClock b t : ℂ) • Rf

theorem continuous_canonicalCplGen (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {b : ℝ} (hb : 0 < b) :
    Continuous (canonicalCplGen lam κ l q Rf b) := by
  have hc : Continuous fun t => (canonicalClock b t : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_canonicalClock hb)
  show Continuous fun t => Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
    (canonicalClock b t * κ) • (1 : B0010.XG →L[ℂ] B0010.XG) + (canonicalClock b t : ℂ) • Rf
  exact (continuous_const.sub ((hc.mul continuous_const).smul continuous_const)).add
    (hc.smul continuous_const)

theorem norm_canonicalCplGen_le (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    ‖canonicalCplGen lam κ l q Rf b t‖ ≤
      ‖Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q‖ +
        b⁻¹ * ‖κ‖ + b⁻¹ * ‖Rf‖ := by
  have h0 := canonicalClock_pos hb t
  have h1 := canonicalClock_le hb t
  have hn1 : ‖(canonicalClock b t * κ) • (1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤ b⁻¹ * ‖κ‖ := by
    calc ‖(canonicalClock b t * κ) • (1 : B0010.XG →L[ℂ] B0010.XG)‖
        = ‖(canonicalClock b t : ℂ) * κ‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ := norm_smul _ _
      _ ≤ ‖(canonicalClock b t : ℂ) * κ‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = canonicalClock b t * ‖κ‖ := by
          rw [mul_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0.le]
      _ ≤ b⁻¹ * ‖κ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hn2 : ‖(canonicalClock b t : ℂ) • Rf‖ ≤ b⁻¹ * ‖Rf‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h0.le]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hs := norm_sub_le (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q)
    ((canonicalClock b t * κ) • (1 : B0010.XG →L[ℂ] B0010.XG))
  have ha := norm_add_le (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
    (canonicalClock b t * κ) • (1 : B0010.XG →L[ℂ] B0010.XG)) ((canonicalClock b t : ℂ) • Rf)
  unfold canonicalCplGen
  linarith

/-- The complementary generator `canonicalCplGen` as an `Evolution.BoundedPert` on the forward
block `[a,e]` (continuous, `‖B(t)‖ ≤ ‖L₀ - λ - P‖ + b⁻¹(|κ| + ‖R_f‖)`). -/
def canonicalCplPert (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {b : ℝ} (hb : 0 < b) (a e : ℝ) :
    Evolution.BoundedPert B0010.XG a e :=
  Evolution.BoundedPert.ofAEStronglyMeasurable (canonicalCplGen lam κ l q Rf b)
    (continuous_canonicalCplGen lam κ l q Rf hb).aestronglyMeasurable
    ⟨_, fun t _ => norm_canonicalCplGen_le lam κ l q Rf hb t⟩

/-! ### The conjugated full coefficient, the gauge, and the backward Duhamel form -/

/-- The conjugated full coefficient `L₀ - λ - κ/σ` (lines 1095-1101: `W = e^{λθ}θ^κV` solves
`-W' = (L - λ + θ⁻¹(D - κ))W`). -/
def canonicalFullGen (lam κ : ℂ) (σ : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
    (κ * (σ : ℂ)⁻¹) • (1 : B0010.XG →L[ℂ] B0010.XG)

/-- The normalization factor `e^{-λθ}θ^{-κ} = exp(-(λθ + κ log θ))` (line 1095, `θ > 0`; "all
positive real powers use the real logarithm", line 1177). -/
def canonicalGauge (lam κ : ℂ) (θ : ℝ) : ℂ := Complex.exp (-(lam * θ + κ * Real.log θ))

/-- **Backward Duhamel form** on `[b,∞)` with respect to the free evolution
`E(θ,σ) = e^{(log σ - log θ)D}`, bounded coefficient `K` and source `g`: for `b ≤ θ ≤ s₀` the
integrand is interval integrable and
`X(θ) = E(θ,s₀)X(s₀) + ∫_θ^{s₀} E(θ,σ)(K(σ)X(σ) + g(σ)) dσ`
(the mild form of `-X' = (θ⁻¹D + K)X + g` with data at `s₀`; lines 1117-1119). -/
def BwdMild (b : ℝ) (K : ℝ → B0010.XG →L[ℂ] B0010.XG) (g X : ℝ → B0010.XG) : Prop :=
  ∀ θ s₀ : ℝ, b ≤ θ → θ ≤ s₀ →
    IntervalIntegrable (fun σ => B0123.expD (Real.log σ - Real.log θ) (K σ (X σ) + g σ))
      volume θ s₀ ∧
    X θ = B0123.expD (Real.log s₀ - Real.log θ) (X s₀) +
      ∫ σ in θ..s₀, B0123.expD (Real.log σ - Real.log θ) (K σ (X σ) + g σ)

/-! ### Open leaves -/

/-- **Leaf 1: the amplitude equation in free Duhamel form** (lines 1097-1101, `-A' = θ⁻¹ℓ(Dr)`,
and its integrated form `A(θ) = A(s₀) + ∫_θ^{s₀} ℓ(Dr(s))/s ds`, lines 1117-1119): for
`q ∈ 𝒟(D)`, `b > 0` and continuous `A, f` on `[b,∞)` with `A(θ) = A(s₀) + ∫_θ^{s₀} f` for
`b ≤ θ ≤ s₀`, the vector `A(θ)q` solves the free Duhamel equation with coefficient `0` and source
`f(σ)q - σ⁻¹A(σ)Dq`:
`A(θ)q = e^{(log s₀-log θ)D}(A(s₀)q) + ∫_θ^{s₀} e^{(log σ-log θ)D}(f(σ)q - σ⁻¹A(σ)Dq) dσ`.

Sketch: fix `b ≤ θ ≤ s₀` (if `θ = s₀` both sides agree, `B0123.expD_zero`).  Put
`k(τ) = A(τ) • e^{(log τ - log θ)D}q`.  For `θ < τ < s₀`: `HasDerivAt A (-f τ) τ` (the equation at
`(τ,s₀)` and `intervalIntegral.integral_hasDerivAt_left`, `f` continuous at `τ`), and
`HasDerivAt (fun τ => e^{(log τ - log θ)D}q) (τ⁻¹ • e^{(log τ - log θ)D}(Dq)) τ`
(`hasDerivAt_expD_logSub_domain`, proved below), so by `HasDerivAt.smul`
`k'(τ) = e^{(log τ - log θ)D}(-f(τ)q + τ⁻¹A(τ)Dq)`.  `k` is continuous on `[θ,s₀]`
(`Short.Spine.CanonicalMild.continuousOn_expD_pair`, `Short.Spine.CanonicalMild.continuousOn_log_sub`),
the derivative is interval integrable (`Short.Spine.CanonicalMild.intervalIntegrable_expD_log`),
so `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` gives
`k(s₀) - k(θ) = ∫_θ^{s₀} k'`, with `k(θ) = A(θ)q`.  The integrability component of `BwdMild` is
the same `intervalIntegrable_expD_log`.  (Alternative, coefficientwise: `B0094.ext_inner_basis`,
`B0123.inner_expD`, `B0123.expMult_of_nonneg`, `B0123.inner_D`, as in
`Short.Spine.CanonicalMild.coeff_duhamel`.) -/
def AmplitudeFreeDuhamel : Prop :=
  ∀ (q : B0010.XG) (hq : q ∈ B0094.D.domain) (b : ℝ), 0 < b →
    ∀ A f : ℝ → ℂ, ContinuousOn A (Ici b) → ContinuousOn f (Ici b) →
      (∀ θ s₀ : ℝ, b ≤ θ → θ ≤ s₀ → A θ = A s₀ + ∫ s in θ..s₀, f s) →
        BwdMild b (fun _ => 0) (fun σ => f σ • q - (A σ / (σ : ℂ)) • B0094.D ⟨q, hq⟩)
          (fun θ => A θ • q)

/-- **Leaf 2: undoing the normalization** (line 1095, `V = e^{-λθ}θ^{-κ}W`): if `W` is continuous
on `[b,∞)`, `b > 0`, and satisfies, for `b ≤ θ ≤ τ ≤ s₀`,
`E(θ,τ)W(τ) = E(θ,s₀)W(s₀) + ∫_τ^{s₀} E(θ,σ)(L₀ - λ - κ/σ)W(σ) dσ`
(`E(θ,σ) = e^{(log σ - log θ)D}`; this is `bwdMild_pullback` of the free Duhamel form of `W`
with coefficient `canonicalFullGen`), then `e^{-λθ}θ^{-κ}W` (`canonicalGauge`) solves the free
Duhamel form with coefficient `L₀` and source `0`.

Sketch: fix `b ≤ θ ≤ s₀`; `h(τ) = E(θ,s₀)W(s₀) + ∫_τ^{s₀} E(θ,σ)K(σ)W(σ) dσ` equals `E(θ,τ)W(τ)`
on `[θ,s₀]` (the hypothesis); `G(τ) = canonicalGauge λ κ τ • h(τ)`.  For `θ < τ < s₀`,
`HasDerivAt h (-(E(θ,τ)K(τ)W(τ))) τ` (`intervalIntegral.integral_hasDerivAt_left`; the integrand
is continuous on `[θ,∞)` by `Short.Spine.CanonicalMild.continuousOn_expD_pair`, continuity of
`σ ↦ K(σ)` and of `W`), and `hasDerivAt_canonicalGauge` (proved below) with `HasDerivAt.smul`
gives `G'(τ) = -(λ + κτ⁻¹)c(τ)h(τ) - c(τ)E(θ,τ)K(τ)W(τ) = -E(θ,τ)L₀(c(τ)W(τ))`,
`c = canonicalGauge λ κ` (use `h(τ) = E(θ,τ)W(τ)` and `K(τ) = L₀ - λ - κτ⁻¹`, so
`(λ + κτ⁻¹)W + K(τ)W = L₀W`).  `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` on
`[θ,s₀]` (continuity of `G` from `intervalIntegral.continuousOn_primitive_interval_left` or the
identity `h = E(θ,·)W`) gives `G(s₀) - G(θ) = -∫_θ^{s₀} E(θ,τ)L₀V(τ) dτ`, `G(θ) = V(θ)`,
`G(s₀) = E(θ,s₀)V(s₀)`.  Integrability: `Short.Spine.CanonicalMild.intervalIntegrable_expD_log`. -/
def BwdGauge : Prop :=
  ∀ (lam κ : ℂ) (b : ℝ), 0 < b → ∀ W : ℝ → B0010.XG, ContinuousOn W (Ici b) →
    (∀ θ τ s₀ : ℝ, b ≤ θ → θ ≤ τ → τ ≤ s₀ →
      B0123.expD (Real.log τ - Real.log θ) (W τ) =
        B0123.expD (Real.log s₀ - Real.log θ) (W s₀) +
          ∫ σ in τ..s₀, B0123.expD (Real.log σ - Real.log θ) (canonicalFullGen lam κ σ (W σ))) →
      BwdMild b (fun _ => Planar.L0) 0 (fun θ => canonicalGauge lam κ θ • W θ)

/-! ### Proved steps -/

/-- The derivative of the gauge: `d/dθ e^{-λθ}θ^{-κ} = -(λ + κ/θ) e^{-λθ}θ^{-κ}`, `θ > 0`. -/
theorem hasDerivAt_canonicalGauge (lam κ : ℂ) {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (canonicalGauge lam κ) (-(lam + κ * (θ : ℂ)⁻¹) * canonicalGauge lam κ θ) θ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => ((Real.log x : ℝ) : ℂ)) ((θ⁻¹ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_log hθ.ne').ofReal_comp
  have h3 : HasDerivAt (fun x : ℝ => -(lam * (x : ℂ) + κ * ((Real.log x : ℝ) : ℂ)))
      (-(lam * 1 + κ * ((θ⁻¹ : ℝ) : ℂ))) θ :=
    ((h1.const_mul lam).add (h2.const_mul κ)).neg
  have h4 := h3.cexp
  have hfun : canonicalGauge lam κ =
      fun x : ℝ => Complex.exp (-(lam * (x : ℂ) + κ * ((Real.log x : ℝ) : ℂ))) := rfl
  rw [hfun]
  convert h4 using 1
  rw [Complex.ofReal_inv]
  ring

/-- The free evolution on `𝒟(D)`: for `0 < θ < τ` and `z ∈ 𝒟(D)`,
`d/dτ e^{(log τ - log θ)D}z = τ⁻¹ e^{(log τ - log θ)D}Dz` (`Short.Spine.hasDerivAt_expD_domain`). -/
theorem hasDerivAt_expD_logSub_domain {θ τ : ℝ} (hθ : 0 < θ) (hθτ : θ < τ)
    (z : B0094.D.domain) :
    HasDerivAt (fun s : ℝ => B0123.expD (Real.log s - Real.log θ) (z : B0010.XG))
      (τ⁻¹ • B0123.expD (Real.log τ - Real.log θ) (B0094.D z)) τ := by
  have ha : 0 < Real.log τ - Real.log θ := sub_pos.mpr (Real.log_lt_log hθ hθτ)
  have h1 := Short.Spine.hasDerivAt_expD_domain ha z
  have hu : HasDerivAt (fun s : ℝ => Real.log s - Real.log θ) τ⁻¹ τ :=
    (Real.hasDerivAt_log (hθ.trans hθτ).ne').sub_const (Real.log θ)
  exact h1.scomp τ hu

/-- **Variation of constants ⇒ mild form** (the `w`-identity in the proof of
`Evolution.mild_unique`): for `U = dyson F A`, `w(t) = U(t,s)z₀ + ∫_s^t U(t,r)ρ(r) dr` satisfies
`w(t) = F(t,s)z₀ + ∫_s^t F(t,r)(A(r)w(r) + ρ(r)) dr`. -/
theorem dyson_variation_mild {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] {a b : ℝ} (F : Evolution.EvolutionFamily X a b)
    (A : Evolution.BoundedPert X a b) {s : ℝ} (hs : a ≤ s) (z₀ : X) {ρ : ℝ → X}
    (hρ : IntegrableOn ρ (Ioc s b)) (t : ℝ) (ht : t ∈ Icc s b) :
    (Evolution.dyson F A).U t s z₀ + ∫ r in s..t, (Evolution.dyson F A).U t r (ρ r) =
      F.U t s z₀ + ∫ r in s..t, F.U t r (A.A r ((Evolution.dyson F A).U r s z₀ +
        ∫ q in s..r, (Evolution.dyson F A).U r q (ρ q)) + ρ r) := by
  set U := Evolution.dyson F A with hU
  have hIc : ContinuousOn (fun t => ∫ r in s..t, U.U t r (ρ r)) (Icc s b) :=
    U.continuousOn_integral_apply hs hρ
  have hρt : IntegrableOn ρ (Ioc s t) := hρ.mono_set (Ioc_subset_Ioc le_rfl ht.2)
  have hi1 : IntervalIntegrable (fun r => F.U t r (A.A r (U.U r s z₀))) volume s t :=
    F.intervalIntegrable_integrand A hs ht.1 ht.2
      ((U.continuousOn_fst hs z₀).mono (Icc_subset_Icc le_rfl ht.2))
  have hi2 : IntervalIntegrable (fun r => F.U t r (A.A r (∫ q in s..r, U.U r q (ρ q))))
      volume s t :=
    F.intervalIntegrable_integrand A hs ht.1 ht.2 (hIc.mono (Icc_subset_Icc le_rfl ht.2))
  have hi3 := F.intervalIntegrable_apply hs ht.1 ht.2 hρt
  have hsplit : ∫ r in s..t, F.U t r (A.A r (U.U r s z₀ + ∫ q in s..r, U.U r q (ρ q)) + ρ r) =
      (∫ r in s..t, F.U t r (A.A r (U.U r s z₀))) +
        ((∫ r in s..t, F.U t r (ρ r)) +
          ∫ r in s..t, F.U t r (A.A r (∫ q in s..r, U.U r q (ρ q)))) := by
    rw [← intervalIntegral.integral_add hi3 hi2, ← intervalIntegral.integral_add hi1
      (hi3.add hi2)]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [map_add]
    abel
  rw [hsplit, ← Evolution.dyson_inhom F A hs ht.1 ht.2 hρt, ← add_assoc, hU,
    Evolution.dyson_left F A ⟨hs, ht.1, ht.2⟩ z₀]

/-- **The complementary evolution is a Dyson evolution on every forward block** (lines
1014-1030, 1102-1104): on `[a,-b]`, `U(t,s) = dyson(freeFam, B)(t,s)`, by
`Evolution.dyson_unique` (the Duhamel field of `IsMildComplementEvolution` with
`e^{D∫_r^tβ} = Cons.G3b.freeU t r`). -/
theorem cplMildIsDyson (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {b : ℝ} (hb : 0 < b)
    {U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hU : IsMildComplementEvolution lam κ l q Rf (canonicalClock b) U) (a : ℝ) :
    ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ -b →
      U t s = (Evolution.dyson (Cons.G3b.freeFam a (-b) (neg_lt_zero.mpr hb))
        (canonicalCplPert lam κ l q Rf hb a (-b))).U t s := by
  refine Evolution.dyson_unique _ _ U (fun s _ _ x => (hU.cont s x).mono Icc_subset_Ici_self) ?_
  intro s t _ hst ht x
  rw [hU.duhamel s t hst x, integral_canonicalClock hb hst ht]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hst] at hr
  show B0123.expD (∫ u in r..t, canonicalClock b u) _ = _
  rw [integral_canonicalClock hb hr.2 ht]
  rfl

/-- **Step 1: the `r`-equation in free Duhamel form** (lines 1097-1104, 1117-1119): the
`r`-equation of the coupled mild system, with the forward complementary evolution
`S(θ,s) = U(-θ,-s)`, is the free Duhamel form of `r` with coefficient `B(-σ)` and source
`σ⁻¹A(σ)y`. -/
theorem complementFreeDuhamel (lam κ : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {b : ℝ} (hb : 0 < b)
    {U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hU : IsMildComplementEvolution lam κ l q Rf (canonicalClock b) U)
    (y : B0010.XG) {A : ℝ → ℂ} {r : ℝ → B0010.XG} (hAc : ContinuousOn A (Ici b))
    (hrc : ContinuousOn r (Ici b))
    (hr : ∀ θ s₀ : ℝ, b ≤ θ → θ ≤ s₀ →
      r θ = canonicalS U θ s₀ (r s₀) + ∫ s in θ..s₀, (A s / s) • canonicalS U θ s y) :
    BwdMild b (fun σ => canonicalCplGen lam κ l q Rf b (-σ)) (fun σ => (A σ / σ) • y) r := by
  intro θ s₀ hθ hθs
  have hθ0 : 0 < θ := hb.trans_le hθ
  have hsrc : ContinuousOn (fun σ : ℝ => (A σ / (σ : ℂ)) • y) (Ici b) := by
    refine (hAc.div Complex.continuous_ofReal.continuousOn fun σ hσ => ?_).smul
      continuousOn_const
    exact Complex.ofReal_ne_zero.mpr (hb.trans_le hσ).ne'
  have hgen : ContinuousOn (fun σ => canonicalCplGen lam κ l q Rf b (-σ) (r σ)) (Ici b) :=
    ((continuous_canonicalCplGen lam κ l q Rf hb).comp continuous_neg).continuousOn.clm_apply hrc
  refine ⟨Short.Spine.CanonicalMild.intervalIntegrable_expD_log hθ0 hθs
    ((hgen.add hsrc).mono fun σ hσ => hθ.trans hσ.1), ?_⟩
  have he : -b < 0 := neg_lt_zero.mpr hb
  have hid := cplMildIsDyson lam κ l q Rf hb hU (-s₀)
  -- the forward source `ρ(u) = A(-u)/(-u) • y` on the block `[-s₀, -b]`
  have hρc : ContinuousOn (fun u : ℝ => (A (-u) / ((-u : ℝ) : ℂ)) • y) (Icc (-s₀) (-b)) :=
    hsrc.comp continuous_neg.continuousOn fun u hu => by
      simp only [mem_Ici]
      linarith [hu.2]
  have hρi : IntegrableOn (fun u : ℝ => (A (-u) / ((-u : ℝ) : ℂ)) • y) (Ioc (-s₀) (-b)) :=
    hρc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- the forward `r`-equation on the block
  have hfwd : ∀ t ∈ Icc (-s₀) (-b), r (-t) =
      (Evolution.dyson (Cons.G3b.freeFam (-s₀) (-b) he)
          (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U t (-s₀) (r s₀) +
        ∫ u in (-s₀)..t, (Evolution.dyson (Cons.G3b.freeFam (-s₀) (-b) he)
          (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U t u
            ((A (-u) / ((-u : ℝ) : ℂ)) • y) := by
    intro t ht
    rw [hr (-t) s₀ (by linarith [ht.2]) (by linarith [ht.1])]
    have hS : canonicalS U (-t) s₀ = (Evolution.dyson (Cons.G3b.freeFam (-s₀) (-b) he)
        (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U t (-s₀) := by
      simp only [canonicalS, neg_neg]
      exact hid (-s₀) t le_rfl ht.1 ht.2
    rw [hS]
    congr 1
    have hc := intervalIntegral.integral_comp_neg (a := -s₀) (b := t)
      (f := fun s : ℝ => (A s / (s : ℂ)) • canonicalS U (-t) s y)
    simp only [neg_neg] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht.1] at hu
    simp only [canonicalS, neg_neg]
    rw [hid u t hu.1 hu.2 ht.2, map_smul]
  have hvm := dyson_variation_mild (Cons.G3b.freeFam (-s₀) (-b) he)
    (canonicalCplPert lam κ l q Rf hb (-s₀) (-b)) (le_refl (-s₀)) (r s₀) hρi (-θ)
    ⟨by linarith, by linarith⟩
  have hθfwd := hfwd (-θ) ⟨by linarith, by linarith⟩
  rw [neg_neg] at hθfwd
  refine hθfwd.trans (hvm.trans ?_)
  congr 1
  · show Cons.G3b.freeU (-θ) (-s₀) (r s₀) = _
    simp only [Cons.G3b.freeU, neg_neg]
  · calc ∫ u in (-s₀)..(-θ), (Cons.G3b.freeFam (-s₀) (-b) he).U (-θ) u
          ((canonicalCplPert lam κ l q Rf hb (-s₀) (-b)).A u
            ((Evolution.dyson (Cons.G3b.freeFam (-s₀) (-b) he)
                (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U u (-s₀) (r s₀) +
              ∫ v in (-s₀)..u, (Evolution.dyson (Cons.G3b.freeFam (-s₀) (-b) he)
                (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U u v
                  ((A (-v) / ((-v : ℝ) : ℂ)) • y)) +
            (A (-u) / ((-u : ℝ) : ℂ)) • y)
        = ∫ u in (-s₀)..(-θ), Cons.G3b.freeU (-θ) u
            (canonicalCplGen lam κ l q Rf b u (r (-u)) + (A (-u) / ((-u : ℝ) : ℂ)) • y) := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [uIcc_of_le (by linarith)] at hu
          show Cons.G3b.freeU (-θ) u (canonicalCplGen lam κ l q Rf b u _ + _) = _
          rw [← hfwd u ⟨hu.1, by linarith [hu.2]⟩]
      _ = ∫ σ in θ..s₀, Cons.G3b.freeU (-θ) (-σ)
            (canonicalCplGen lam κ l q Rf b (-σ) (r (-(-σ))) +
              (A (-(-σ)) / ((-(-σ) : ℝ) : ℂ)) • y) :=
          (intervalIntegral.integral_comp_neg (a := θ) (b := s₀)
            (f := fun u : ℝ => Cons.G3b.freeU (-θ) u
              (canonicalCplGen lam κ l q Rf b u (r (-u)) +
                (A (-u) / ((-u : ℝ) : ℂ)) • y))).symm
      _ = _ := by
          refine intervalIntegral.integral_congr fun σ _ => ?_
          simp only [Cons.G3b.freeU, neg_neg]

/-- **Step 3: the generator algebra** (lines 1097-1101 and `seedRf_spec`): for `σ ≥ b > 0`
and `r = w - ℓ(w)q ∈ ker ℓ`,
`(L - λ - κ/σ)w = B(-σ)r + σ⁻¹ℓ(w)QDq + σ⁻¹ℓ(Dr)q - σ⁻¹ℓ(w)Dq`. -/
theorem canonicalGen_algebra {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {qd : B0010.XG} (hq : q ∈ B0094.D.domain)
    (hqd : qd ∈ B0094.D.domain) {b σ : ℝ} (hbσ : b ≤ σ) (w : B0010.XG) :
    canonicalFullGen lam (seedKappa l q hq) σ w =
      (canonicalCplGen lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) b (-σ)
          (w - l w • q) + (l w / (σ : ℂ)) • seedQDq l q hq) +
        ((seedLD qd hqd (w - l w • q) / (σ : ℂ)) • q - (l w / (σ : ℂ)) • B0094.D ⟨q, hq⟩) := by
  have hclk : ((canonicalClock b (-σ) : ℝ) : ℂ) = (σ : ℂ)⁻¹ := by
    rw [canonicalClock_eq (by linarith), neg_neg, Complex.ofReal_inv]
  have hL : Planar.L0 q = lam • q := hI.eigen
  have hlq : l q = 1 := hI.ell_q
  simp only [canonicalFullGen, canonicalCplGen, seedRf, seedQDq, seedLD, hclk,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, map_sub, map_smul,
    hL, hlq, smul_eq_mul, sub_self, zero_sub]
  module

/-- **The integrand algebra of step 3** as a statement (task `PartI:C07/1/1/2/4`; lines
1097-1101): it is `canonicalGen_algebra`. -/
def CanonicalIntegrandAlgebra : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG) (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b σ : ℝ), b ≤ σ →
      ∀ w : B0010.XG,
        canonicalFullGen lam (seedKappa l q hq) σ w =
          (canonicalCplGen lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) b (-σ)
              (w - l w • q) + (l w / (σ : ℂ)) • seedQDq l q hq) +
            ((seedLD qd hqd (w - l w • q) / (σ : ℂ)) • q - (l w / (σ : ℂ)) • B0094.D ⟨q, hq⟩)

example : CanonicalIntegrandAlgebra := fun _ _ _ hI _ hq hqd _ _ hbσ w =>
  canonicalGen_algebra hI hq hqd hbσ w

/-- `X ↦ BwdMild b K g X` respects pointwise equality on `[b,∞)`. -/
theorem bwdMild_congr {b : ℝ} {K : ℝ → B0010.XG →L[ℂ] B0010.XG} {g X Y : ℝ → B0010.XG}
    (h : BwdMild b K g X) (hXY : ∀ θ, b ≤ θ → X θ = Y θ) : BwdMild b K g Y := by
  intro θ s₀ hθ hθs
  obtain ⟨hi, he⟩ := h θ s₀ hθ hθs
  have hEq : EqOn (fun σ => B0123.expD (Real.log σ - Real.log θ) (K σ (X σ) + g σ))
      (fun σ => B0123.expD (Real.log σ - Real.log θ) (K σ (Y σ) + g σ)) (uIcc θ s₀) := by
    intro σ hσ
    rw [uIcc_of_le hθs] at hσ
    simp only [hXY σ (hθ.trans hσ.1)]
  refine ⟨(intervalIntegrable_congr (hEq.mono uIoc_subset_uIcc)).mp hi, ?_⟩
  rw [← hXY θ hθ, ← hXY s₀ (hθ.trans hθs), he, intervalIntegral.integral_congr hEq]

/-- **Superposition** of two backward Duhamel forms whose integrands add up. -/
theorem bwdMild_add {b : ℝ} {K K₁ K₂ : ℝ → B0010.XG →L[ℂ] B0010.XG}
    {g g₁ g₂ X X₁ X₂ : ℝ → B0010.XG}
    (h₁ : BwdMild b K₁ g₁ X₁) (h₂ : BwdMild b K₂ g₂ X₂)
    (hX : ∀ θ, b ≤ θ → X θ = X₁ θ + X₂ θ)
    (hK : ∀ σ, b ≤ σ → K σ (X σ) + g σ = (K₁ σ (X₁ σ) + g₁ σ) + (K₂ σ (X₂ σ) + g₂ σ)) :
    BwdMild b K g X := by
  intro θ s₀ hθ hθs
  obtain ⟨i₁, e₁⟩ := h₁ θ s₀ hθ hθs
  obtain ⟨i₂, e₂⟩ := h₂ θ s₀ hθ hθs
  have hEq : EqOn (fun σ => B0123.expD (Real.log σ - Real.log θ) (K σ (X σ) + g σ))
      (fun σ => B0123.expD (Real.log σ - Real.log θ) (K₁ σ (X₁ σ) + g₁ σ) +
        B0123.expD (Real.log σ - Real.log θ) (K₂ σ (X₂ σ) + g₂ σ)) (uIcc θ s₀) := by
    intro σ hσ
    rw [uIcc_of_le hθs] at hσ
    simp only [hK σ (hθ.trans hσ.1), map_add]
  refine ⟨(intervalIntegrable_congr (hEq.mono uIoc_subset_uIcc)).mpr (i₁.add i₂), ?_⟩
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_add i₁ i₂, hX θ hθ,
    hX s₀ (hθ.trans hθs), map_add, e₁, e₂]
  abel

/-- **Intermediate times** (the evolution law `E(θ,τ)E(τ,σ) = E(θ,σ)`, `B0123.expD_add`): a
backward Duhamel form at `(τ,s₀)`, transported by `E(θ,τ)`, `b ≤ θ ≤ τ ≤ s₀`. -/
theorem bwdMild_pullback {b : ℝ} {K : ℝ → B0010.XG →L[ℂ] B0010.XG} {g X : ℝ → B0010.XG}
    (hb : 0 < b) (h : BwdMild b K g X) {θ τ s₀ : ℝ} (hθ : b ≤ θ) (hθτ : θ ≤ τ)
    (hτs : τ ≤ s₀) :
    B0123.expD (Real.log τ - Real.log θ) (X τ) =
      B0123.expD (Real.log s₀ - Real.log θ) (X s₀) +
        ∫ σ in τ..s₀, B0123.expD (Real.log σ - Real.log θ) (K σ (X σ) + g σ) := by
  obtain ⟨hi, he⟩ := h τ s₀ (hθ.trans hθτ) hτs
  have hθ0 : 0 < θ := hb.trans_le hθ
  have hτ0 : 0 < τ := hθ0.trans_le hθτ
  have hcomp : ∀ v, τ ≤ v → ∀ x, B0123.expD (Real.log τ - Real.log θ)
      (B0123.expD (Real.log v - Real.log τ) x) = B0123.expD (Real.log v - Real.log θ) x := by
    intro v hv x
    have hsum : Real.log v - Real.log θ =
        (Real.log τ - Real.log θ) + (Real.log v - Real.log τ) := by ring
    rw [hsum, B0123.expD_add (sub_nonneg.mpr (Real.log_le_log hθ0 hθτ))
      (sub_nonneg.mpr (Real.log_le_log hτ0 hv)), ContinuousLinearMap.comp_apply]
  rw [he, map_add, hcomp s₀ hτs, ← (B0123.expD (Real.log τ - Real.log θ)).intervalIntegral_comp_comm hi]
  congr 1
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le hτs] at hσ
  exact hcomp σ hσ.1 _

/-- **Step 5a: the gauge recovers `V`**: `e^{-λθ}θ^{-κ}·e^{λθ}θ^κV(θ) = V(θ)` for `θ > 0`. -/
theorem canonicalGauge_smul_canonicalW (lam κ : ℂ) (V : ℝ → B0010.XG) {θ : ℝ} (hθ : 0 < θ) :
    canonicalGauge lam κ θ • canonicalW lam κ V θ = V θ := by
  unfold canonicalGauge canonicalW
  rw [smul_smul, smul_smul]
  have hpow : (θ : ℂ) ^ κ = Complex.exp ((Real.log θ : ℂ) * κ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hθ.ne'),
      ← Complex.ofReal_log hθ.le]
  rw [hpow, ← Complex.exp_add, ← Complex.exp_add]
  have h0 : -(lam * (θ : ℂ) + κ * (Real.log θ : ℂ)) + lam * (θ : ℂ) +
      (Real.log θ : ℂ) * κ = 0 := by ring
  rw [h0, Complex.exp_zero, one_smul]

/-- **Step 5b: the change of variables `u = -σ`** turns the free Duhamel form with coefficient
`L₀` into `FullMildEq` (cf. `Short.Spine.CanonicalMild.S_mild_interval`). -/
theorem fullMildEq_of_bwdMild {b : ℝ} {V : ℝ → B0010.XG}
    (h : BwdMild b (fun _ => Planar.L0) 0 V) : FullMildEq b V := by
  intro θ θ' hθ hθθ'
  rw [(h θ θ' hθ hθθ').2]
  congr 1
  have hc := intervalIntegral.integral_comp_neg (a := θ) (b := θ')
    (f := fun u : ℝ => Cons.G3b.freeU (-θ) u (B0012.L0 (V (-u))))
  simp only [neg_neg] at hc
  rw [← hc]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [Cons.G3b.freeU, neg_neg, Pi.zero_apply, add_zero]
  rfl

/-! ### Assembly -/

/-- **`CoupledImpliesFullMild` from the two leaves** (lines 1094-1125). -/
theorem coupledImpliesFullMild_of (hAmp : AmplitudeFreeDuhamel) (hG : BwdGauge) :
    CoupledImpliesFullMild := by
  intro lam q l hI qd _ hq hqd b hb V hV
  obtain ⟨hVc, U, hU, hcm⟩ := hV
  have hWc := continuousOn_canonicalW hb lam (seedKappa l q hq) hVc
  have hAc : ContinuousOn (fun θ => l (canonicalW lam (seedKappa l q hq) V θ)) (Ici b) :=
    l.continuous.comp_continuousOn hWc
  have hrc : ContinuousOn (fun θ => canonicalW lam (seedKappa l q hq) V θ -
      l (canonicalW lam (seedKappa l q hq) V θ) • q) (Ici b) :=
    hWc.sub (hAc.smul continuousOn_const)
  have h1 := complementFreeDuhamel lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) hb hU
    (seedQDq l q hq) hAc hrc (fun θ s₀ h1 h2 => (hcm θ s₀ h1 h2).1)
  have hfc : ContinuousOn (fun σ : ℝ => seedLD qd hqd (canonicalW lam (seedKappa l q hq) V σ -
      l (canonicalW lam (seedKappa l q hq) V σ) • q) / (σ : ℂ)) (Ici b) :=
    ((seedLD qd hqd).continuous.comp_continuousOn hrc).div
      Complex.continuous_ofReal.continuousOn
      fun σ hσ => Complex.ofReal_ne_zero.mpr (hb.trans_le hσ).ne'
  have h2 := hAmp q hq b hb _ _ hAc hfc (fun θ s₀ h1 h2 => (hcm θ s₀ h1 h2).2)
  have h3 : BwdMild b (canonicalFullGen lam (seedKappa l q hq)) 0
      (canonicalW lam (seedKappa l q hq) V) := by
    refine bwdMild_add h1 h2 (fun θ _ => (sub_add_cancel _ _).symm) fun σ hσ => ?_
    simp only [Pi.zero_apply, add_zero, ContinuousLinearMap.zero_apply, zero_add]
    exact canonicalGen_algebra hI hq hqd hσ _
  have h5 := hG lam (seedKappa l q hq) b hb _ hWc fun θ τ s₀ hθ hθτ hτs => by
    simpa only [Pi.zero_apply, add_zero] using bwdMild_pullback hb h3 hθ hθτ hτs
  exact fullMildEq_of_bwdMild (bwdMild_congr h5 fun θ hθ =>
    canonicalGauge_smul_canonicalW lam (seedKappa l q hq) V (hb.trans_le hθ))

end UnforcedLeray.Short.PartI
