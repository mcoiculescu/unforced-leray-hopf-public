import UnforcedLeray.Short.PartI.Sub.PartI_C05

/-!
# Part I, task `PartI:C05/4`: invariance of `ker ℓ` under the mild complementary evolution

Source of record: `the November 2 reference manuscript`, lines 1056-1058
("testing the mild equation against `q†` in `dom D`").

The source computation is reduced to the scalar integral identity `MildPairingIdentity`
(`h(t) = ℓ x - ∫_s^t h`, with `h(r) = ℓ(U r s x)`), from which `mildComplementInvariant_of`
derives `ℓ(U t s x) = e^{-(t-s)} ℓ x` by the scalar ODE argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.Short.PartI

/-- The left eigenfunctional identity `ℓ(L₀ y) = λ ℓ(y)` for the Riesz projection `P = qℓ`
of `IsSeedXG` (from `IsSeedXG.proj`; source lines 970-975). -/
def MildEllL0 : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ y : B0010.XG, l (Planar.L0 y) = lam * l y

/-- Testing the Gaussian diffusion semigroup against `q†` with a *measurable* clock
(lines 1056-1058; the continuous-clock version is `Cons.G3b.expD_timeChange_inner_generator`):
for `qd ∈ dom D`, `0 ≤ β ≤ 1` measurable and `r ≤ t`,
`⟨qd, e^{(∫_r^t β) D} z⟩ = ⟨qd, z⟩ + ∫_r^t β(τ) ⟨D qd, e^{(∫_r^τ β) D} z⟩ dτ`.
Sketch: coordinatewise in the oscillator basis (`B0123.inner_expD`), where it is the scalar
identity `e^{-nB(t)} = 1 - n ∫ β e^{-nB}` for the absolutely continuous clock `B(τ)=∫_r^τ β`. -/
def ExpDPairingMeasurable : Prop :=
  ∀ (qd : B0010.XG) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ), Measurable β →
    (∀ t, 0 ≤ β t ∧ β t ≤ 1) → ∀ r t : ℝ, r ≤ t → ∀ z : B0010.XG,
      inner ℂ qd (B0123.expD (∫ u in r..t, β u) z) = inner ℂ qd z +
        ∫ τ in r..t, (β τ : ℂ) *
          inner ℂ (B0094.D ⟨qd, hqd⟩) (B0123.expD (∫ u in r..τ, β u) z)

/-- **The scalar mild identity** (lines 1056-1058): for a mild complementary evolution,
`h(t) = ℓ x - ∫_s^t h` with `h(r) = ℓ(U(r,s)x)`.  Sketch: apply `ℓ = ⟨qd, ·⟩` to the Duhamel
identity, `ℓ(e^{aD} y) = ⟨e^{aD} qd, y⟩` (`expD` selfadjoint for `a ≥ 0`), expand
`e^{(∫_r^t β) D} qd` with `ExpDPairingMeasurable` and use Fubini; with `ℓ L₀ = λ ℓ` (`MildEllL0`),
`ℓ q = 1`, `ℓ(R_f y) = κ ℓ y - ⟨D qd, y⟩` (from `seedRf`) the `β`-terms cancel:
`ℓ(G_r y) = -ℓ y - β(r) ⟨D qd, y⟩`, and `⟨D qd, e^{aD} w⟩` terms recombine into
`⟨D qd, U(τ,s) x⟩`, which is cancelled. -/
def MildPairingIdentity : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ),
      Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
      ∀ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd β U →
        ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
          l (U t s x) = l x - ∫ r in s..t, l (U r s x)

/-- Scalar ODE step: a continuous `h` on `[s,∞)` with `h(t) = h(s) - ∫_s^t h` is
`h(s) e^{-(t-s)}`. -/
theorem scalar_integral_eq_exp (s : ℝ) (h : ℝ → ℂ) (hc : ContinuousOn h (Ici s))
    (hh : ∀ t, s ≤ t → h t = h s - ∫ r in s..t, h r) :
    ∀ t, s ≤ t → h t = (Real.exp (-(t - s)) : ℂ) * h s := by
  intro t hst
  set H : ℝ → ℂ := fun u => ∫ r in s..u, h r with hH
  set k : ℝ → ℂ := fun u => (h s - H u) * Complex.exp ((u : ℂ) - s) with hk
  have hint : ∀ x, s ≤ x → IntervalIntegrable h volume s x := fun x hx =>
    (hc.mono (by
      intro y hy
      rw [uIcc_of_le hx] at hy
      exact hy.1)).intervalIntegrable
  have hderH : ∀ x, s ≤ x → HasDerivWithinAt H (h x) (Ici x) x := by
    intro x hx
    have hsub : Ici x ⊆ Ici s := Ici_subset_Ici.2 hx
    have hsub' : Ioi x ⊆ Ici s := Ioi_subset_Ici_self.trans hsub
    have hmeas : StronglyMeasurableAtFilter h (𝓝[Ioi x] x) volume :=
      (hc.mono hsub').stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi x
    have hcw : ContinuousWithinAt h (Ioi x) x :=
      ((hc.mono hsub) x (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self
    exact intervalIntegral.integral_hasDerivWithinAt_right (hint x hx) hmeas hcw
  have hkd : ∀ x ∈ Ico s t, HasDerivWithinAt k 0 (Ici x) x := by
    intro x hx
    have h1 : HasDerivWithinAt (fun u => h s - H u) (-(h x)) (Ici x) x :=
      ((hderH x hx.1)).const_sub (h s)
    have h2 : HasDerivWithinAt (fun u : ℝ => Complex.exp ((u : ℂ) - s))
        (Complex.exp ((x : ℂ) - s)) (Ici x) x := by
      have : HasDerivAt (fun u : ℝ => Complex.exp ((u : ℂ) - s)) (Complex.exp ((x : ℂ) - s)) x := by
        have h3 : HasDerivAt (fun u : ℝ => (u : ℂ) - s) 1 x :=
          (Complex.ofRealCLM.hasDerivAt).sub_const (s : ℂ)
        simpa using h3.cexp
      exact this.hasDerivWithinAt
    have h4 := h1.mul h2
    have : h s - H x = h x := by simp only [hH]; rw [hh x hx.1]
    have e : (-h x * Complex.exp ((x : ℂ) - s) + (h s - H x) * Complex.exp ((x : ℂ) - s)) = 0 := by
      rw [this]; ring
    rw [e] at h4
    exact h4
  have hkcont : ContinuousOn k (Icc s t) := by
    have hHc : ContinuousOn H (Icc s t) := by
      have := intervalIntegral.continuousOn_primitive_interval' (hint t hst)
        (show s ∈ uIcc s t from left_mem_uIcc)
      rwa [uIcc_of_le hst] at this
    have hE : Continuous fun u : ℝ => Complex.exp ((u : ℂ) - s) := by fun_prop
    exact ((continuousOn_const.sub hHc).mul hE.continuousOn)
  have hconst := constant_of_has_deriv_right_zero hkcont hkd t ⟨hst, le_rfl⟩
  have hks : k s = h s := by simp [hk, hH]
  have hkt : k t = h t * Complex.exp ((t : ℂ) - s) := by
    simp only [hk, hH]; rw [← hh t hst]
  rw [hks, hkt] at hconst
  have hne : Complex.exp ((t : ℂ) - s) ≠ 0 := Complex.exp_ne_zero _
  have : h t = h s * (Complex.exp ((t : ℂ) - s))⁻¹ := by
    field_simp; exact hconst
  rw [this, ← Complex.exp_neg]
  have : (Real.exp (-(t - s)) : ℂ) = Complex.exp (-((t : ℂ) - s)) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [this]; ring

/-- The target from the scalar integral identity. -/
theorem mildComplementInvariant_of (hM : MildPairingIdentity) : MildComplementInvariant := by
  intro lam q l hseed qd hl hq hqd β hβm hβ U hU s t hst x
  have hc : ContinuousOn (fun r => l (U r s x)) (Ici s) :=
    l.continuous.comp_continuousOn (hU.cont s x)
  have key := scalar_integral_eq_exp s (fun r => l (U r s x)) hc
    (fun t ht => by
      have := hM lam q l hseed qd hl hq hqd β hβm hβ U hU s t ht x
      simpa [hU.self_eq] using this) t hst
  simpa [hU.self_eq] using key

end UnforcedLeray.Short.PartI
