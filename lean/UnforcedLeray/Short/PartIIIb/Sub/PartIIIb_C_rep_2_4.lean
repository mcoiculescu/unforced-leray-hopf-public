import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs

/-!
# `PartIII-b:C/rep/2/4` : the outward primitive in phase supremum (`OutPrimPhaseBound`)

Source `the November 2 reference manuscript` 4181-4192 (`Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,0,z) dρ`,
"the separated-kernel estimates prove convergence of this primitive"), 3603-3647 (`sep:kernel`,
`sep:resolvent`, `sep:young`).

Decomposition.  `outPrimAbsLe` (proved): `|Ψ_Z| ≤ ∫_r^∞ ρ |Z_z|`.  `OutPrimPointwise`: for
`Z = Re W_μ` and `Z = X₀`, at half-plane points `|Ψ_Z(r,z)| ≤ C₀ · outMaj` where `outMaj` is the
`ρ`-weighted integral of the order-`0` majorant `sepDom` along the half-line `(ρ,0,z)`, `ρ ≥ r`.
`OutMajAnnulus` is the analytic core (the `ρ`-integral of the gap kernel, Hölder over the old disk,
Young in the vertical variable, Minkowski in `λ`, periodic phase sum).  `outPrimPhaseBound_of` proves
the target from these.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `ρ`-weighted order-`0` majorant along the half-line: `∫_r^∞ ρ · sepDom a 0 D g (τ, (ρ,0,z)) dρ`
(source 4181-4192, 3611-3623). -/
def outMaj (a D : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ r z : ℝ) : ℝ≥0∞ :=
  ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * IIIa.sepDom a 0 D g τ !₂[ρ, 0, z]

/-- `|Ψ_Z(r,z)| ≤ ∫_r^∞ ρ |Z_z(ρ,0,z)| dρ` (norm of a Bochner integral, also when not integrable). -/
theorem outPrimAbsLe (Z : ℝ → Space → Space) (τ r z : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal |outPrim Z τ r z| ≤
      ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * ‖Z τ !₂[ρ, 0, z] 2‖ₑ := by
  unfold outPrim
  rw [abs_neg, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine setLIntegral_mono' measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ0 : 0 ≤ ρ := hr.trans (le_of_lt hρ)
  rw [enorm_mul, Real.enorm_eq_ofReal hρ0]

theorem sepDom_anti_a {a b : ℝ} (hab : a ≤ b) (D : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ)
    (y : Space) : IIIa.sepDom b 0 D g τ y ≤ IIIa.sepDom a 0 D g τ y := by
  unfold IIIa.sepDom
  refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hl.1 hl.2.le hab)) le_rfl

theorem outMaj_anti_a {a b : ℝ} (hab : a ≤ b) (D : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ r z : ℝ) :
    outMaj b D g τ r z ≤ outMaj a D g τ r z := by
  unfold outMaj
  gcongr with ρ
  exact sepDom_anti_a hab D g τ _

/-- **Pointwise domination of the outward primitive** (source 4181-4192 with 3604-3623): with
`g = srcNorm T`, `D = r_i - r_o`, half-plane points `(ρ,0,z)`, `ρ ≥ r ≥ r_i`, and
`|Z_z| ≤ |W_μ|` resp. `|X₀,z| ≤ |W_μ| + |W_{μ+1}|`. -/
def OutPrimPointwise : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∃ C0 : ℝ, 0 ≤ C0 ∧
    ∀ (ν μ rOut rIn P : ℝ), 0 < ν → μ ∈ Icc σ₁ σ₂ → 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T, IIIa.IsSepSource P rOut T → ∀ (τ r z : ℝ), rIn ≤ r →
        ENNReal.ofReal |outPrim (sepWre ν μ T) τ r z| ≤
            ENNReal.ofReal C0 * outMaj (2 * μ + 2) (rIn - rOut) (IIIa.srcNorm T) τ r z ∧
        ENNReal.ofReal |outPrim (sepX0 ν μ T) τ r z| ≤
            ENNReal.ofReal C0 * (2 * outMaj (2 * μ + 2) (rIn - rOut) (IIIa.srcNorm T) τ r z)

/-- `OutPrimPointwise` from the order-`0` domination `IIIa.sepWDominated_zero`. -/
theorem outPrimPointwise_of (hA : IIIa.SepWDominated) (hK : IIIa.SepKernelBounds) :
    OutPrimPointwise := by
  intro σ₁ σ₂ hσ
  obtain ⟨C0, hC0, hdom⟩ := IIIa.sepWDominated_zero hA hK
  refine ⟨C0, hC0, ?_⟩
  intro ν μ rOut rIn P hν hμ hrO hrr hP T hT τ r z hr
  have hrIn : 0 < rIn := by linarith
  have hcomp : ∀ (m : ℝ), -(1 / 4) < m → ∀ ρ : ℝ, rIn ≤ ρ →
      ‖sepWre ν m T τ !₂[ρ, 0, z] 2‖ₑ ≤ ENNReal.ofReal C0 *
        IIIa.sepDom (2 * m + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z] := by
    intro m hm ρ hρ
    have hy : rIn ≤ Real.sqrt ((!₂[ρ, 0, z] : Space) 0 ^ 2 + (!₂[ρ, 0, z] : Space) 1 ^ 2) := by
      simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [show ρ ^ 2 + (0:ℝ) ^ 2 = ρ ^ 2 by ring, Real.sqrt_sq (by linarith)]
      exact hρ
    have h1 := hdom ν hν (m : ℂ) (by simpa using hm) rOut rIn P hrO hrr hP T hT τ _ hy
    refine le_trans ?_ (by simpa using h1)
    unfold IIIa.wDerivNorm
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_zero]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : ‖sepWre ν m T τ !₂[ρ, 0, z] 2‖ ≤ ‖IIIa.sepW ν (m : ℂ) T !₂[ρ, 0, z] τ 2‖ := by
      simp only [sepWre, PiLp.toLp_apply, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    exact h2.trans (norm_le_pi_norm (IIIa.sepW ν (m : ℂ) T !₂[ρ, 0, z] τ) 2)
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hint : ∀ (Z : ℝ → Space → Space) (B : ℝ → ℝ≥0∞),
      (∀ ρ, rIn ≤ ρ → ‖Z τ !₂[ρ, 0, z] 2‖ₑ ≤ B ρ) →
      ENNReal.ofReal |outPrim Z τ r z| ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * B ρ := by
    intro Z B hB
    refine (outPrimAbsLe Z τ r z (by linarith)).trans ?_
    refine setLIntegral_mono' measurableSet_Ioi (fun ρ hρ => ?_)
    exact mul_le_mul' le_rfl (hB ρ (hr.trans (le_of_lt hρ)))
  constructor
  · refine (hint _ (fun ρ => ENNReal.ofReal C0 *
      IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z])
      (fun ρ hρ => hcomp μ hμ' ρ hρ)).trans ?_
    unfold outMaj
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_of_eq (lintegral_congr fun ρ => ?_)
    ring
  · have hB : ∀ ρ, rIn ≤ ρ → ‖sepX0 ν μ T τ !₂[ρ, 0, z] 2‖ₑ ≤ ENNReal.ofReal C0 * (2 *
        IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z]) := by
      intro ρ hρ
      have e : sepX0 ν μ T τ !₂[ρ, 0, z] 2 =
          sepWre ν μ T τ !₂[ρ, 0, z] 2 - sepWre ν (μ + 1) T τ !₂[ρ, 0, z] 2 := by
        rw [sepX0_eq_sub]; rfl
      rw [e]
      refine (enorm_sub_le).trans ?_
      have h1 := hcomp μ hμ' ρ hρ
      have h2 := hcomp (μ + 1) (by linarith) ρ hρ
      have h3 := sepDom_anti_a (a := 2 * μ + 2) (b := 2 * (μ + 1) + 2) (by linarith)
        (rIn - rOut) (IIIa.srcNorm T) τ !₂[ρ, 0, z]
      calc _ ≤ ENNReal.ofReal C0 * IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ
              !₂[ρ, 0, z] + ENNReal.ofReal C0 * IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut)
              (IIIa.srcNorm T) τ !₂[ρ, 0, z] :=
            add_le_add h1 (h2.trans (mul_le_mul' le_rfl h3))
        _ = _ := by rw [← mul_add, ← two_mul]
    refine (hint _ _ hB).trans ?_
    unfold outMaj
    rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by simp),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_of_eq (lintegral_congr fun ρ => ?_)
    ring

/-! ## The analytic core: reduction to the vertical variable

Restored statements of the decomposition (tasks `PartIII-b:C/rep/2/4/1` .. `/7`).  Lengths: `rIn = R√ν`,
`rOut = R√(5ν/6)`, `D = rIn - rOut`, `κ = rIn / D`. -/

/-- The vertical kernel `rIn/(2D(D²+t²))` (source 4181-4192: `∫_r^∞ ρ|(ρ,0,z) - λz'|^{-4} dρ`
with the gap `D`, `ρ ≤ (r_i/D)(ρ - r_o)`). -/
def vertKern (rIn D t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (rIn / (2 * D * (D ^ 2 + t ^ 2)))

/-- The horizontal integral `vprof g τ s = ∫∫ g(τ,(x,y,s)) dx dy` (for `g` supported in the old
disk, the integral over the disk, source 5219-5221). -/
def vprof (g : ℝ → Space → ℝ≥0∞) (τ s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ∫⁻ y : ℝ, g τ !₂[x, y, s]

/-- The one-dimensional dilation integral `∫_0^1 λ^a ∫ k(z - λs) h(τ + 2 log λ, s) ds dλ` with the
vertical kernel `k = vertKern rIn D`. -/
def vertRedH (a rIn D : ℝ) (h : ℝ → ℝ → ℝ≥0∞) (τ z : ℝ) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
    ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s

/-- `vertRedH` for the vertical profile of `g`. -/
def vertRed (a rIn D : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ z : ℝ) : ℝ≥0∞ :=
  vertRedH a rIn D (vprof g) τ z

/-- The `L^q(ℝ)` norm of a nonnegative function of one variable. -/
def lqNorm1 (q : ℝ) (f : ℝ → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ s : ℝ, f s ^ q) ^ (1 / q)

/-- The mixed norm `((1/P)∫_0^P (∫ h(τ,s)^q ds)^{2/q} dτ)^{1/2}` for functions of `(τ, s) ∈ ℝ²`. -/
def ltauLq1 (P q : ℝ) (h : ℝ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, (∫⁻ s : ℝ, h τ s ^ q) ^ (2 / q)) ^ (1 / 2 : ℝ)

/-- **(1) The `ρ`-integral of the gap kernel** (source 4181-4192, 3603-3610): for `0 ≤ r_o < r_i`,
`D = r_i - r_o`, `r ≥ r_i`, `0 < λ < 1`, a source point `z'` with `|z'_h| ≤ r_o`:
`∫_r^∞ ρ · 1_{|x|≥D}|x|^{-4} dρ ≤ vertKern r_i D (z - λz'_3)`, `x = (ρ,0,z) - λz'`. -/
def OutMajRho : Prop :=
  ∀ (rOut rIn : ℝ), 0 ≤ rOut → rOut < rIn → ∀ (r z l : ℝ) (z' : Space), rIn ≤ r → 0 < l → l < 1 →
    ϱ z' ≤ rOut →
      ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * IIIa.sepKd 0 (rIn - rOut) (!₂[ρ, 0, z] - l • z') ≤
        vertKern rIn (rIn - rOut) (z - l * z' 2)

/-- **(2) Reduction to the vertical profile** (Tonelli in `(ρ, λ, z')`, `OutMajRho`, horizontal
integration of `z'`; source 4181-4192). -/
def OutMajReduce : Prop :=
  ∀ (a rOut rIn : ℝ), 0 ≤ rOut → rOut < rIn → ∀ g : ℝ → Space → ℝ≥0∞,
    Measurable (Function.uncurry g) → (∀ τ z, rOut < ϱ z → g τ z = 0) →
      ∀ (τ r z : ℝ), rIn ≤ r →
        outMaj a (rIn - rOut) g τ r z ≤ vertRed a rIn (rIn - rOut) g τ z

/-- **(3) Hölder over the old disk** (source 5219-5221, exponent `1/p' = 3/22`, `|disk| = π r_o²`):
`‖vprof g‖_{L²_τL^{22/19}_s} ≤ (π r_o²)^{3/22} ‖g‖_{L²_τL^{22/19}_y}` for `g` supported in
`ϱ ≤ r_o`. -/
def VprofHolder : Prop :=
  ∀ (rOut P : ℝ), 0 ≤ rOut → 0 < P → ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
    (∀ τ z, rOut < ϱ z → g τ z = 0) →
      ltauLq1 P (22 / 19) (vprof g) ≤
        ENNReal.ofReal ((Real.pi * rOut ^ 2) ^ (3 / 22 : ℝ)) * IIIa.ltauLq P (22 / 19) g

/-- **(4) Measurability** of the vertical profile and of the reduced integral (Tonelli). -/
def VertMeasurable : Prop :=
  ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
    Measurable (Function.uncurry (vprof g)) ∧
      ∀ a rIn D : ℝ, Measurable (Function.uncurry (vertRed a rIn D g))

/-- **(5) Young in the vertical variable, Minkowski in `λ`, phase sum** (source 3624-3647,
5219-5221 in one dimension; `‖(D²+t²)^{-1}‖_{L^{11/3}(ℝ)} = C D^{-2+3/11}`, Young
`1 + 3/22 = 19/22 + 3/11`, dilation `λ^{-1+19/22}`, `a ≥ 3/2`, `P ≤ 1`):
`‖vertRedH a rIn D h (τ,·)‖_{L^{22/3}} ≤ C (rIn/D) D^{-2+3/11} ‖h‖_{L²_τL^{22/19}_s}`. -/
def VertYoungPhase : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (a rIn D P : ℝ), 3 / 2 ≤ a → 0 < D → 0 < rIn → 0 < P → P ≤ 1 →
    ∀ h : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry h) → (∀ τ s, h (τ + P) s = h τ s) →
      ∀ τ : ℝ, lqNorm1 (22 / 3) (vertRedH a rIn D h τ) ≤
        ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) * ltauLq1 P (22 / 19) h

/-- **(6) Fubini on the transition annulus** (source 4164-4167): the annulus
`R√ν ≤ ϱ ≤ R√(5ν/4)` has horizontal area `π ν R²/4`, so for a function of the height only,
`‖1_ann F(y₃)‖_{L^{22/3}(ℝ³)} = (π ν R²/4)^{3/22} ‖F‖_{L^{22/3}(ℝ)}`. -/
def AnnulusFubini : Prop :=
  ∀ (ν R : ℝ), 0 < ν → 0 < R → ∀ F : ℝ → ℝ≥0∞, Measurable F →
    lqNorm (22 / 3) ((streamAnn ν R).indicator (fun y => F (y 2))) =
      ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) * lqNorm1 (22 / 3) F

/-- **(7) The analytic core** (source 4181-4192 with 3603-3647, 5219-5221): with
`rIn = R√ν`, `rOut = R√(5ν/6)`, for a `P`-periodic measurable `g` supported in `ϱ ≤ rOut`, `a ≥ 3/2`,
`0 < P ≤ 1`, at every phase,
`‖1_ann outMaj a (rIn - rOut) g τ (ϱ y) (y₃)‖_{L^{22/3}_y} ≤ C (R√ν)^{-13/11} ‖g‖_{L²_τL^{22/19}}`. -/
def OutMajAnnulus : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R P a : ℝ), 0 < ν → 0 < R → 0 < P → P ≤ 1 → 3 / 2 ≤ a →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) → ∀ τ : ℝ,
        lqNorm (22 / 3) ((streamAnn ν R).indicator (fun y =>
            outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
          ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ))) * IIIa.ltauLq P (22 / 19) g


theorem lqNorm_ind_const_mul {q : ℝ} (hq : 0 < q) (S : Set Space) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (f : Space → ℝ≥0∞) :
    lqNorm q (S.indicator (fun y => c * f y)) = c * lqNorm q (S.indicator f) := by
  have : S.indicator (fun y => c * f y) = fun y => c * S.indicator f y := by
    funext y
    by_cases hy : y ∈ S <;> simp [Set.indicator, hy]
  rw [this]
  exact lqNorm_const_mul hq c hc _

theorem srcNorm_measurable {P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P rOut T) : Measurable (Function.uncurry (IIIa.srcNorm T)) := by
  unfold IIIa.srcNorm IIIa.tensorNorm Function.uncurry
  refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (hT.measurable i j).pow_const 2

/-- **The outward primitive in phase supremum** from the pointwise domination and the analytic core. -/
theorem outPrimPhaseBound_of (hP : OutPrimPointwise) (hA : OutMajAnnulus) : OutPrimPhaseBound := by
  intro σ₁ σ₂ hσ
  obtain ⟨C0, hC0, hpt⟩ := hP σ₁ σ₂ hσ
  obtain ⟨C, hC, hann⟩ := hA
  refine ⟨2 * C0 * C, by positivity, ?_⟩
  intro ν μ R P hν hR hP0 hP1 hμ T hT _hmom τ
  have hrO0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by nlinarith)) hR
  have ha : 3 / 2 ≤ 2 * μ + 2 := by linarith [hμ.1]
  have key := hann ν R P (2 * μ + 2) hν hR hP0 hP1 ha (IIIa.srcNorm T) (srcNorm_measurable hT)
    (fun τ z => by simp only [IIIa.srcNorm, hT.periodic τ z])
    (fun τ z hz => by simp [IIIa.srcNorm, hT.support τ z hz, IIIa.tensorNorm]) τ
  set X : ℝ := (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ)) with hX
  have hX0 : 0 ≤ X := by positivity
  set F := IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)
  set M : Space → ℝ≥0∞ := fun y => outMaj (2 * μ + 2) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
    (IIIa.srcNorm T) τ (ϱ y) (y 2) with hM
  have hpt' := fun (y : Space) (hy : y ∈ streamAnn ν R) =>
    hpt ν μ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hrO0 hlt hP0 T hT τ (ϱ y) (y 2) hy.1
  have hq : (0 : ℝ) < 22 / 3 := by norm_num
  constructor
  · calc _ ≤ lqNorm (22 / 3) ((streamAnn ν R).indicator (fun y => ENNReal.ofReal C0 * M y)) := by
          refine lqNorm_mono hq fun y => ?_
          by_cases hy : y ∈ streamAnn ν R
          · simp only [Set.indicator_of_mem hy]; exact (hpt' y hy).1
          · simp [Set.indicator_of_notMem hy]
      _ = ENNReal.ofReal C0 * lqNorm (22 / 3) ((streamAnn ν R).indicator M) :=
          lqNorm_ind_const_mul hq _ _ ENNReal.ofReal_ne_top _
      _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal (C * X) * F) := by gcongr
      _ ≤ ENNReal.ofReal (2 * C0 * C * X) * F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC0]
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          nlinarith [mul_nonneg hC0 (mul_nonneg hC hX0)]
  · calc _ ≤ lqNorm (22 / 3) ((streamAnn ν R).indicator
            (fun y => (ENNReal.ofReal C0 * 2) * M y)) := by
          refine lqNorm_mono hq fun y => ?_
          by_cases hy : y ∈ streamAnn ν R
          · simp only [Set.indicator_of_mem hy]
            refine (hpt' y hy).2.trans (le_of_eq ?_)
            rw [mul_assoc]
          · simp [Set.indicator_of_notMem hy]
      _ = (ENNReal.ofReal C0 * 2) * lqNorm (22 / 3) ((streamAnn ν R).indicator M) :=
          lqNorm_ind_const_mul hq _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)) _
      _ ≤ (ENNReal.ofReal C0 * 2) * (ENNReal.ofReal (C * X) * F) := by gcongr
      _ = ENNReal.ofReal (2 * C0 * C * X) * F := by
          have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          rw [this, ← mul_assoc, ← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
