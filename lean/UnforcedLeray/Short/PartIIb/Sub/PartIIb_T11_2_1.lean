import UnforcedLeray.Short.PartIIb.Sub.T11_2

/-!
# Part II-b, leaf `PartII-b:T11/2/1` (`DualFLocInt`): decomposition into six leaves

Source: `the November 2 reference manuscript` 1923-1927 (flat equation, duality
pairing).  `F = dualF` is locally integrable on `(0, s)`:

* `DualFMeas`      (`T11/2/1/1`): `F` is a.e.-strongly measurable on `(0,s)` (Fubini);
* `DualFPointwise` (`T11/2/1/2`): cell Hölder, a.e. `σ ∈ (0,s)`:
  `‖F σ‖ ≤ 2 σ^{Re μ} A(σ) B(s-σ)`, `A(σ) = ‖b(σ,·)‖_{L^r(avgμ)}`,
  `B(τ) = ‖∇^⊥H(τ,·)‖_{L^{r'}(avgμ)}`;
* `DualFAFinite`   (`T11/2/1/3`): `∫_0^∞ σ^{r/2-5/2} A(σ)^r dσ < ∞` (from `InHr`, Tonelli);
* `DualFBFinite`   (`T11/2/1/4`): `∫_{τ₁}^{τ₂} B(τ)^{r'} dτ < ∞` (`HeatSol.deriv_memLp`, `n = 1`);
* `DualFABMeas`    (`T11/2/1/5`): `A`, `B` are a.e.-measurable on `(0,∞)`;
* `SigmaHolder`    (`T11/2/1/6`): Hölder in `σ` on a compact `K ⊂ (0,s)`.

Proved here: `dualFLocInt_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `A(σ) = ‖b(σ,·)‖_{L^r(avgμ c)}`. -/
def dfA (c r : ℝ) (b : CProf) (σ : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun p : ℝ × ℝ => b (σ, p)) (ENNReal.ofReal r) (Cyl.avgμ c)

/-- `B(τ) = ‖∇^⊥H(τ,·)‖_{L^{r'}(avgμ c)}`. -/
def dfB (c r' : ℝ) (H : Coord → ℝ) (τ : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun p : ℝ × ℝ => perpGrad (fun z => H (τ, z)) p) (ENNReal.ofReal r') (Cyl.avgμ c)

/-- Leaf `T11/2/1/1`: `dualF` is a.e.-strongly measurable on `(0,s)` (Fubini,
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`). -/
def DualFMeas : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → IsFlatResponse ν μ 0 b →
    HeatSol c ν (r / (r - 1)) H →
    AEStronglyMeasurable (dualF c μ b H s) (volume.restrict (Ioo (0 : ℝ) s))

/-- Leaf `T11/2/1/2`: cell Hölder, for a.e. `σ ∈ (0,s)`. (`|Σ bᵢ gᵢ| ≤ √2 ‖b‖‖g‖_∞`, so the
constant `2` is safe; `‖σ^μ‖ = σ^{Re μ}` for `σ > 0`.) -/
def DualFPointwise : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → IsFlatResponse ν μ 0 b →
    HeatSol c ν (r / (r - 1)) H →
    ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)),
      ‖dualF c μ b H s σ‖ₑ ≤
        2 * (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ * dfB c (r / (r - 1)) H (s - σ))

/-- Leaf `T11/2/1/3`: `∫_{σ>0} σ^{r/2-5/2} A(σ)^r < ∞`, since `hNorm c r b ^ r =
∫ ‖b‖^r d(ageμ c (r/2-5/2))` and `ageμ` is `(σ^a dσ|_{σ>0}) ⊗ avgμ` (`Axi.lintegral_ageμ`,
Tonelli). -/
def DualFAFinite : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → InHr c r b →
    ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) * dfA c r b σ ^ r < ⊤

/-- Leaf `T11/2/1/4`: `∫_{τ₁}^{τ₂} B(τ)^{r'} dτ < ∞` for `0 < τ₁ ≤ τ₂`, from
`HeatSol.deriv_memLp` with `n = 1` (`ageμ c 0 = dτ ⊗ avgμ` on `τ > 0`; relate `perpGrad` to
`iteratedFDeriv ℝ 1 H`). -/
def DualFBFinite : Prop :=
  ∀ (c r ν : ℝ) (H : Coord → ℝ), 0 < c → 0 < ν → 1 < r → HeatSol c ν (r / (r - 1)) H →
    ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₂ →
      ∫⁻ τ in Icc τ₁ τ₂, dfB c (r / (r - 1)) H τ ^ (r / (r - 1)) < ⊤

/-- Leaf `T11/2/1/5`: measurability of `A` and `B` on `(0,∞)` (Tonelli:
`Measurable.lintegral_prod_right'`; `b` strongly measurable for `hMeas`, `H` smooth on `τ>0`). -/
def DualFABMeas : Prop :=
  ∀ (c r ν : ℝ) (b : CProf) (H : Coord → ℝ), 0 < c → 0 < ν → 1 < r → InHr c r b →
    HeatSol c ν (r / (r - 1)) H →
    AEMeasurable (dfA c r b) (volume.restrict (Ioi (0 : ℝ))) ∧
      AEMeasurable (dfB c (r / (r - 1)) H) (volume.restrict (Ioi (0 : ℝ)))

/-- Leaf `T11/2/1/6` (pure real analysis, Hölder in `σ`): with `1 < r`, `A, B` a.e.-measurable on
`(0,∞)`, `∫ σ^{r/2-5/2} A^r < ∞` and `∫_{[τ₁,τ₂]} B^{r'} < ∞`, the function
`σ ↦ σ^e A(σ) B(s-σ)` has finite integral on every compact `K ⊂ (0,s)`.  (On `K ⊂ [a,a']`,
`a > 0`, write `σ^e A B(s-σ) = (σ^{e - (r/2-5/2)/r}) · (σ^{(r/2-5/2)/r} A) · B(s-σ)`, the first
factor bounded, Hölder with exponents `r, r'`, and `σ ↦ s - σ` maps `K` into `[s-a', s-a]`.) -/
def SigmaHolder : Prop :=
  ∀ (r e s : ℝ) (A B : ℝ → ℝ≥0∞), 1 < r → 0 < s →
    AEMeasurable A (volume.restrict (Ioi (0 : ℝ))) →
    AEMeasurable B (volume.restrict (Ioi (0 : ℝ))) →
    ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) * A σ ^ r < ⊤ →
    (∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₂ → ∫⁻ τ in Icc τ₁ τ₂, B τ ^ (r / (r - 1)) < ⊤) →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (0 : ℝ) s →
      ∫⁻ σ in K, ENNReal.ofReal (σ ^ e) * A σ * B (s - σ) < ⊤

/-- `DualFLocInt` from the six leaves. -/
theorem dualFLocInt_of (hm : DualFMeas) (hp : DualFPointwise) (hA : DualFAFinite)
    (hB : DualFBFinite) (hab : DualFABMeas) (hh : SigmaHolder) : DualFLocInt := by
  intro c r ν μ b H s hc hν hr hs hb hfl hH
  rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
  intro K hK hKc
  refine ⟨(hm c r ν μ b H s hc hν hr hs hb hfl hH).mono_measure
    (Measure.restrict_mono hK le_rfl), ?_⟩
  have hae : ∀ᵐ σ : ℝ ∂(volume.restrict K),
      ‖dualF c μ b H s σ‖ₑ ≤
        2 * (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) :=
    ae_restrict_of_ae_restrict_of_subset hK (hp c r ν μ b H s hc hν hr hs hb hfl hH)
  have hfin := hh r μ.re s (dfA c r b) (dfB c (r / (r - 1)) H) hr hs
    (hab c r ν b H hc hν hr hb hH).1 (hab c r ν b H hc hν hr hb hH).2
    (hA c r b hc hr hb) (hB c r ν H hc hν hr hH) K hKc hK
  unfold HasFiniteIntegral
  calc ∫⁻ σ in K, ‖dualF c μ b H s σ‖ₑ
      ≤ ∫⁻ σ in K, 2 * (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ *
          dfB c (r / (r - 1)) H (s - σ)) := lintegral_mono_ae hae
    _ = 2 * ∫⁻ σ in K, ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ *
          dfB c (r / (r - 1)) H (s - σ) := lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hfin

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.dualFLocInt_of
