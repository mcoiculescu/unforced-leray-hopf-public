import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_org
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2

/-!
# `SFCProjGrad` from the slice-wise description of `P₀` (organize task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/3/org`)

Source `the November 2 reference manuscript`
1650-1656 (`T₀ = R₀ P₀`, `P₀` the ordinary planar cylinder Leray projection), 1676 (`P₀` is the
`ε = 0` member of the conjugated projections), 1684-1689 (the classical case: `g` smooth with compact
support, the flat equation), 3426-3430 (`∇b ∈ L²_loc((0,∞);L²)`).

`P₀ f' = PepsC 0 c f'` is an `L²` class on the profile cell.  The route to its smooth representative:

* (L, `SFCLiftForce`) the lift `f'` of an `IsSmoothForce` `g` is its smooth representative `F`
  (complexified), `measureH`-a.e.;
* (a, `PepsC0Slices`) `PepsC 0 c` acts on each age slice as the planar cylinder projection
  `IIIa.P0C` of `Short/PartIII-a/Sub/T18_2_4_2.lean` (flat profile coordinates; the weight
  `s^{-3/2}` of `measureH` does not depend on `(q, η)`);
* (c, `P0SmoothFamily`) the projected slices `P0C c (F(σ, ·))` have a measurable, `q`-periodic
  family of `C^∞`, bounded representatives `Ψ(σ, ·)` (order-zero multiplier commuting with `∂_q, ∂_η`);
* (b, `P0GradContract`) on such a representative `‖∇Ψ(σ)‖_{L²(cell)} ≤ ‖∇F(σ)‖_{L²(cell)}`
  (`IIIa.P0CommWeakC`, built as `p0CommWeakC`: weak derivatives commute with `P₀`; `‖P₀‖ ≤ 1`);
* (`SmoothForceGradBound`) `‖∇F(σ)‖_{L²(cell)}` is bounded uniformly in `σ`.

`sfcProjGrad_of` takes `Gs(σ, y) = σ⁻¹ Ψ(σ, y)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 P0C HasWeakCellDerivC)

/-- A `ℂ²`-vector as an element of `MeridC = EuclideanSpace ℂ (Fin 2)`. -/
def toMC (v : Fin 2 → ℂ) : UnforcedLeray.B0223.MeridC := WithLp.toLp 2 v

/-! ## The leaves -/

/-- **(L) The lift of a smooth force is the complexified force** (source 1684-1689; the
recentring `NearInst.cellPt` of the profile cell `q ∈ (0, c]` onto `q ∈ [-c/2, c/2)`, source 2667,
is harmless since the fields are `c`-periodic in `q`).  If `g` is represented `ageμ`-a.e. by a
`c`-periodic `F`, every lift `f'` of `g` (`SFCLift`) equals `p ↦ F(p)` (complexified)
`measureH`-a.e. -/
def SFCLiftForce : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Hsp c) (F : Chart → Fin 2 → ℝ),
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) →
    (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC g p i = ((F p i : ℝ) : ℂ)) →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
      (f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] fun p => toMC fun i => ((F p i : ℝ) : ℂ)

/-- **(a) `P₀ = PepsC 0 c` acts slice by slice as the planar cylinder projection** (source
1650-1656, 1676: `P₀` is the ordinary planar cylinder Leray projection).  At `ε = 0`,
`cgrad 0 Φ = (∂_qΦ, ∂_ηΦ)` and the weight `s^{-3/2}` of `measureH` does not depend on `(q, η)`, so
`solenoidalHC 0 c` consists of the `b` whose slices `b(σ, ·)` are weakly divergence free on the
cylinder for a.e. `σ`, and its orthogonal projection is `P0C` (`Short/PartIII-a/Sub/T18_2_4_2.lean`:
`Cyl.P0` on the real and imaginary parts) slice by slice.  Precisely: if `f' = Φ` `measureH`-a.e.
with `Φ` measurable and `c`-periodic in `q`, and `Ψ` is measurable, `c`-periodic in `q`, with
`Ψ(σ, ·) = P0C c (Φ(σ, ·))` a.e. on the cell `[-c/2, c/2) × ℝ` for every `σ > 0`, then
`PepsC 0 c f' = Ψ` `measureH`-a.e. -/
def PepsC0Slices : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (Φ Ψ : Chart → Fin 2 → ℂ),
    (∀ i, Measurable fun p => Φ p i) → (∀ i, Measurable fun p => Ψ p i) →
    (∀ s q η, Φ (s, (q + c, η)) = Φ (s, (q, η))) →
    (∀ s q η, Ψ (s, (q + c, η)) = Ψ (s, (q, η))) →
    (f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => toMC (Φ p)) →
    (∀ σ : ℝ, 0 < σ →
      (fun y => Ψ (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c (fun y => Φ (σ, y))) →
    (UnforcedLeray.Short.PartIIa.PepsC 0 c f' :
        UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => toMC (Ψ p))

/-- **(c) Smooth representatives of the projected slices** (source 1650-1656, 1676: `P₀` is a
Fourier multiplier of order zero in `(q, η)` commuting with `∂_q, ∂_η`; for the weak derivatives this
is `IIIa.P0CommWeakC`, built; source 1684-1689: `F` is `C^∞`, `c`-periodic, supported in
`s ∈ [s₀, s₁]`, `|η| ≤ L`, so every `∂^α P₀ F(σ) = P₀ ∂^α F(σ)` is in `L²` of the cell and the
projected slice has a `C^∞` bounded representative).  There is a measurable `Ψ`, `c`-periodic in `q`,
such that for every `σ`: `Ψ(σ, ·)` is `C^∞` and bounded, vanishes when `F(σ, ·)` does, and equals
`P0C c (F(σ, ·))` a.e. on the cell `[-c/2, c/2) × ℝ`. -/
def P0SmoothFamily : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun p => F p i) →
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    ∃ Ψ : Chart → Fin 2 → ℂ, (∀ i, Measurable fun p => Ψ p i) ∧
      (∀ s q η, Ψ (s, (q + c, η)) = Ψ (s, (q, η))) ∧
      ∀ σ : ℝ, (∀ i, ContDiff ℝ ∞ fun y : ℝ × ℝ => Ψ (σ, y) i) ∧
        (∃ C' : ℝ, ∀ y : ℝ × ℝ, vnorm2 (Ψ (σ, y)) ≤ C') ∧
        ((∀ y : ℝ × ℝ, F (σ, y) = 0) → ∀ y : ℝ × ℝ, Ψ (σ, y) = 0) ∧
        (fun y => Ψ (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c]
          P0C c (fun y i => ((F (σ, y) i : ℝ) : ℂ))

/-- **(b) Gradient contraction of `P₀` on a smooth representative** (source 1650-1656, 1676: `P₀`
commutes with `∂_q, ∂_η` and is an orthogonal projection).  If `φ` is real, `C^∞`, `c`-periodic in
`q`, vanishing for `|η| > L`, and `ψ` is `C^∞`, `c`-periodic with `ψ = P0C c φ` a.e. on the cell,
then `∫_cell |∇ψ|² ≤ ∫_cell |∇φ|²`.  Route: `IIIa.P0CommWeakC` (built, `p0CommWeakC`) gives
`∂_j P0C φ = P0C ∂_j φ` weakly; the classical derivative of the smooth periodic `ψ` is its weak
derivative; weak derivatives are unique a.e. on the cell; `Cyl.norm_P0_le`. -/
def P0GradContract : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (φ : ℝ × ℝ → Fin 2 → ℝ) (ψ : ℝ × ℝ → Fin 2 → ℂ),
    (∀ i, ContDiff ℝ ∞ fun y => φ y i) → (∀ q η, φ (q + c, η) = φ (q, η)) →
    (∃ L : ℝ, ∀ y : ℝ × ℝ, φ y ≠ 0 → |y.2| ≤ L) →
    (∀ i, ContDiff ℝ ∞ fun y => ψ y i) → (∀ q η, ψ (q + c, η) = ψ (q, η)) →
    ψ =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c (fun y i => ((φ y i : ℝ) : ℂ)) →
    ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ (fun y => ψ y i) x (B0579.dir j)) ^ 2)
      ≤ ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j =>
          ((fderiv ℝ (fun y => φ y i) x (B0579.dir j) : ℝ) : ℂ)) ^ 2)

/-- **Weak cell derivatives are unique a.e.** (used inside `P0GradContract`; the fundamental lemma
of the calculus of variations on the cylinder, source 1650-1656: the weak derivatives of the flat
equation are taken against smooth `c`-periodic tests with compact `η`-support).  Two weak
`j`-derivatives `g₁, g₂` of the same `u` (`IIIa.HasWeakCellDerivC`, whose integrability clauses make
`g₁ - g₂` locally integrable on the cell) agree a.e. on the cell `[-c/2, c/2) × ℝ`. -/
def WeakCellDerivUnique : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (j : Fin 2) (u g₁ g₂ : ℝ × ℝ → ℂ),
    HasWeakCellDerivC c j u g₁ → HasWeakCellDerivC c j u g₂ →
      g₁ =ᵐ[UnforcedLeray.Cyl.cellμ c] g₂

/-- **Gradient energy of a smooth force, uniformly in the age** (source 1684-1689: `g` is `C^∞`,
`c`-periodic, supported in `s ∈ [s₀, s₁]`, `|η| ≤ L`).  `∫_cell |∇_y F(σ, ·)|² ≤ C` for every `σ`:
the continuous `∇F` is bounded on the compact `[s₀, s₁] × [-c/2, c/2] × [-L, L]`, vanishes for
`|η| > L` and outside `[s₀, s₁]`, and `[-c/2, c/2) × [-L, L]` has finite measure. -/
def SmoothForceGradBound : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun p => F p i) →
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    ∃ C : ℝ, ∀ σ : ℝ,
      ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j =>
          ((fderiv ℝ (fun y => F (σ, y) i) x (B0579.dir j) : ℝ) : ℂ)) ^ 2) ≤ ENNReal.ofReal C

/-! ## Small algebra -/

theorem projGrad_toMC_apply (v : Fin 2 → ℂ) (i : Fin 2) : (toMC v) i = v i := rfl

theorem projGrad_norm_toMC (v : Fin 2 → ℂ) : ‖toMC v‖ = vnorm2 v := by
  rw [EuclideanSpace.norm_eq]
  rfl

theorem projGrad_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt (by positivity)]

theorem projGrad_tnorm2_const_mul_sq (a : ℂ) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => a * T i j) ^ 2 = ‖a‖ ^ 2 * tnorm2 T ^ 2 := by
  rw [projGrad_tnorm2_sq, projGrad_tnorm2_sq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_mul, mul_pow]

/-! ## The wiring -/

theorem sfcProjGrad_of (hL : SFCLiftForce) (hA : PepsC0Slices) (hS : P0SmoothFamily)
    (hK : P0GradContract) (hB : SmoothForceGradBound) : SFCProjGrad := by
  intro c ν μ hc R0 g hctx f' hlift
  obtain ⟨F, hFs, hFp, ⟨s0, s1, L, hs0, hFsupp⟩, hFae⟩ := hctx.2.2.2
  have hband : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
    ⟨s0, s1, L, hs0, hFsupp⟩
  obtain ⟨Ψ, hΨm, hΨp, hΨ⟩ := hS c hc F hFs hFp hband
  obtain ⟨C5, hC5⟩ := hB c hc F hFs hFp hband
  have hf' := hL c hc g F hFp hFae f' hlift
  set Φ : Chart → Fin 2 → ℂ := fun p i => ((F p i : ℝ) : ℂ) with hΦdef
  have hΦm : ∀ i, Measurable fun p => Φ p i := fun i =>
    Complex.measurable_ofReal.comp (hFs i).continuous.measurable
  have hΦp : ∀ s q η, Φ (s, (q + c, η)) = Φ (s, (q, η)) := by
    intro s q η
    simp only [hΦdef, hFp]
  have hP := hA c hc f' Φ Ψ hΦm hΨm hΦp hΨp hf' (fun σ _ => (hΨ σ).2.2.2)
  -- the representative `Gs(σ, y) = σ⁻¹ Ψ(σ, y)`
  refine ⟨fun p => toMC (fun i => ((p.1 : ℝ) : ℂ)⁻¹ * Ψ p i), ?_, ⟨s0, hs0, ?_⟩, ?_⟩
  · filter_upwards [hP] with p hp
    unfold sfcGp
    rw [hp]
    ext i
    simp [toMC]
  · intro p hp
    have hz : ∀ y : ℝ × ℝ, F (p.1, y) = 0 := by
      intro y
      by_contra h
      exact absurd (hFsupp (p.1, y) h).1.1 (not_le.2 hp)
    have h0 := (hΨ p.1).2.2.1 hz p.2
    ext i
    simp [toMC, h0]
  · intro s₂ _hs₂
    refine ⟨s0⁻¹ ^ 2 * max C5 0, Filter.Eventually.of_forall fun σ => ?_⟩
    obtain ⟨hsm, ⟨C', hC'⟩, hvan, hae⟩ := hΨ σ
    have happ : ∀ (y : ℝ × ℝ) (i : Fin 2),
        (toMC (fun i => ((σ : ℝ) : ℂ)⁻¹ * Ψ (σ, y) i)) i = ((σ : ℝ) : ℂ)⁻¹ * Ψ (σ, y) i :=
      fun _ _ => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simp only [happ]
      exact contDiff_const.mul (hsm i)
    · intro q η
      simp only [hΨp]
    · refine ⟨‖((σ : ℝ) : ℂ)⁻¹‖ * C', fun y => ?_⟩
      show ‖toMC (fun i => ((σ : ℝ) : ℂ)⁻¹ * Ψ (σ, y) i)‖ ≤ _
      have e : toMC (fun i => ((σ : ℝ) : ℂ)⁻¹ * Ψ (σ, y) i) =
          ((σ : ℝ) : ℂ)⁻¹ • toMC (Ψ (σ, y)) := by
        ext i
        simp [toMC]
      rw [e, norm_smul, projGrad_norm_toMC]
      exact mul_le_mul_of_nonneg_left (hC' y) (norm_nonneg _)
    · -- the gradient energy
      show ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ), ENNReal.ofReal (tnorm2 (fun i j =>
          fderiv ℝ (fun y : ℝ × ℝ => (toMC (fun i => ((σ : ℝ) : ℂ)⁻¹ * Ψ (σ, y) i)) i) x
            (B0579.dir j)) ^ 2) ≤ ENNReal.ofReal (s0⁻¹ ^ 2 * max C5 0)
      set a : ℂ := ((σ : ℝ) : ℂ)⁻¹ with ha
      set S : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) with hSdef
      have hfd : ∀ (x : ℝ × ℝ) (i j : Fin 2),
          fderiv ℝ (fun y : ℝ × ℝ => (toMC (fun i => a * Ψ (σ, y) i)) i) x (B0579.dir j) =
            a * fderiv ℝ (fun y : ℝ × ℝ => Ψ (σ, y) i) x (B0579.dir j) := by
        intro x i j
        have hd : DifferentiableAt ℝ (fun y : ℝ × ℝ => Ψ (σ, y) i) x :=
          ((hsm i).differentiable (by simp)).differentiableAt
        simp only [happ]
        rw [fderiv_const_mul hd]
        rfl
      have hint : ∀ x : ℝ × ℝ,
          ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ
              (fun y : ℝ × ℝ => (toMC (fun i => a * Ψ (σ, y) i)) i) x (B0579.dir j)) ^ 2) =
            ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (tnorm2 (fun i j =>
              fderiv ℝ (fun y : ℝ × ℝ => Ψ (σ, y) i) x (B0579.dir j)) ^ 2) := by
        intro x
        simp only [hfd]
        rw [projGrad_tnorm2_const_mul_sq, ENNReal.ofReal_mul (by positivity)]
      rw [lintegral_congr hint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      by_cases hσ : σ < s0
      · -- `Ψ(σ, ·) = 0`
        have hz : ∀ y : ℝ × ℝ, F (σ, y) = 0 := by
          intro y
          by_contra h
          exact absurd (hFsupp (σ, y) h).1.1 (not_le.2 hσ)
        have h0 := hvan hz
        have hzero : ∀ x : ℝ × ℝ, ENNReal.ofReal (tnorm2 (fun i j =>
            fderiv ℝ (fun y : ℝ × ℝ => Ψ (σ, y) i) x (B0579.dir j)) ^ 2) = 0 := by
          intro x
          have hf : ∀ i : Fin 2, (fun y : ℝ × ℝ => Ψ (σ, y) i) = fun _ => (0 : ℂ) := by
            intro i
            funext y
            rw [h0 y]
            rfl
          simp only [hf]
          simp [tnorm2]
        simp only [hzero, lintegral_zero, mul_zero]
        exact zero_le
      · have hσ0 : s0 ≤ σ := not_lt.1 hσ
        have hσpos : 0 < σ := lt_of_lt_of_le hs0 hσ0
        have hK' := hK c hc (fun y => F (σ, y)) (fun y => Ψ (σ, y))
          (fun i => (hFs i).comp (contDiff_const.prodMk contDiff_id))
          (fun q η => hFp σ q η) ⟨L, fun y hy => (hFsupp (σ, y) hy).2⟩
          hsm (fun q η => hΨp σ q η) hae
        have hle1 := hK'.trans (hC5 σ)
        have hnorm : ‖a‖ = σ⁻¹ := by
          rw [ha, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσpos]
        have ha2 : ‖a‖ ^ 2 ≤ s0⁻¹ ^ 2 := by
          rw [hnorm]
          have : σ⁻¹ ≤ s0⁻¹ := inv_anti₀ hs0 hσ0
          exact pow_le_pow_left₀ (by positivity) this 2
        calc ENNReal.ofReal (‖a‖ ^ 2) * ∫⁻ x in S, ENNReal.ofReal (tnorm2 (fun i j =>
                fderiv ℝ (fun y : ℝ × ℝ => Ψ (σ, y) i) x (B0579.dir j)) ^ 2)
            ≤ ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (max C5 0) := by
              gcongr
              exact hle1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          _ = ENNReal.ofReal (‖a‖ ^ 2 * max C5 0) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal (s0⁻¹ ^ 2 * max C5 0) :=
              ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right ha2 (le_max_right _ _))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
