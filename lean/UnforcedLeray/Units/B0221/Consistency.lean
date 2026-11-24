import UnforcedLeray.Units.B0221.ScalarLift

/-!
# B0221 helper: the conjugated operator acts on smooth profiles as the formula `A_ε`

Blueprint unit B0221 (label `eq:st18-t00114`), `paper/main.tex` lines 3316–3346.

The manuscript defines `A_ε` on `H` as the conjugate of the exact whole-space generator
(tex lines 3341–3347). The generator of the outer semigroup `S_ε(t)` (tex lines 3348–3352,
blueprint unit B0223) is not yet formalized. This file states, as the named hypothesis
`GeneratorOnTestFields`, the one property of that generator used here: on `C²` fields that
vanish near the axis, have bounded support and are `2εc`-periodic in `τ`
(`IsTestField`), it acts as the classical operator `ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ`.

Under it, every `C²` periodic profile with support in a compact age band and a bounded
`η`-range lies in the domain of the conjugate `J_ε⁻¹ G J_ε`, and the conjugate acts on it by the
formula `A_ε = -S + ν s [Q_ε² + ∂_η²]` (`conjOp_eq_Aeps`). The pointwise input is the
conjugation identity `outerGen_liftU`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Topology
open scoped ENNReal
open UnforcedLeray.B0220

namespace UnforcedLeray.B0221

/-! ### `q`-periodicity of the profile operators -/

section Periodic

variable {c : ℝ}

/-- The shift by one `q`-cell. -/
def qShift (c : ℝ) : Profile := (0, c, 0)

theorem add_qShift (c : ℝ) (p : Profile) : p + qShift c = (p.1, p.2.1 + c, p.2.2) := by
  obtain ⟨s, q, η⟩ := p
  simp [qShift]

theorem fderiv_qPeriodic {f : Profile → ℝ} (hf : QPeriodic c f) (p : Profile) :
    fderiv ℝ f (p.1, p.2.1 + c, p.2.2) = fderiv ℝ f p := by
  have hfun : (fun x => f (x + qShift c)) = f := funext fun x => by
    rw [add_qShift]; exact hf x
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := p) (qShift c)
  rw [hfun, add_qShift] at h
  exact h.symm

theorem qPeriodic_fderiv_apply {f : Profile → ℝ} (hf : QPeriodic c f) (v : Profile) :
    QPeriodic c (fun p => fderiv ℝ f p v) := fun p => by
  simp only [fderiv_qPeriodic hf p]

theorem qPeriodic_opQ (ε : ℝ) {f : Profile → ℝ} (hf : QPeriodic c f) :
    QPeriodic c (opQ ε f) := fun p => by
  simp only [opQ, opK, dQ, dS, dEta, fderiv_qPeriodic hf p, hf p]

/-- `A_ε b` is `c`-periodic in `q` when `b` is. -/
theorem qPeriodic_Aeps (ν ε : ℝ) {f : Profile → ℝ} (hf : QPeriodic c f) :
    QPeriodic c (Aeps ν ε f) := fun p => by
  have h1 := qPeriodic_opQ ε hf
  have h2 : QPeriodic c (dEta f) := qPeriodic_fderiv_apply hf eEta
  simp only [Aeps, opS, opQ, opK, dQ, dS, dEta, fderiv_qPeriodic hf p, fderiv_qPeriodic h1 p,
    fderiv_qPeriodic h2 p, hf p]

end Periodic

/-! ### Test fields and the named generator hypothesis -/

/-- The physical test fields: `C²` off the axis, vanishing near the axis (hence `C²` on all of
`ℝ³ × ℝ`), with bounded support in `x`, and `2εc`-periodic in `τ`. -/
structure IsTestField (ε c : ℝ) (u : Space × ℝ → ℝ) : Prop where
  smooth : ∀ y : Space × ℝ, radius y.1 ≠ 0 → ContDiffAt ℝ 2 u y
  axis : ∃ δ > 0, ∀ y : Space × ℝ, radius y.1 < δ → u y = 0
  bounded : ∃ R, ∀ y : Space × ℝ, R < ‖y.1‖ → u y = 0
  periodic : ∀ (x : Space) (τ : ℝ), u (x, τ + 2 * ε * c) = u (x, τ)

/-- **Named hypothesis (the exact whole-space generator on test fields).** `G` is an operator on
`L²(dx dτ)` (one `τ` period) whose domain contains every test field (`IsTestField`) and which
acts on it as the classical operator `ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` (`outerGen`). This holds
for the generator of the time-periodic outer semigroup
`S_ε(t)F(x,τ) = e^{t/2}[e^{νε²(e^t-1)Δ} F(·, τ-t)](e^{t/2}x)` (tex lines 3343–3352, blueprint
unit B0223), whose theory (heat semigroup on `L²`, generator domains) is not yet formalized. -/
def GeneratorOnTestFields (ν ε c : ℝ) (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) : Prop :=
  ∀ u : Space × ℝ → ℝ, IsTestField ε c u → ∀ V : PhysL2sc ε c,
    (V : Space × ℝ → ℝ) =ᵐ[physMeasure ε c] u →
      ∃ h : V ∈ G.domain, (G ⟨V, h⟩ : Space × ℝ → ℝ) =ᵐ[physMeasure ε c] outerGen ν ε u

/-! ### The lift of a compactly supported smooth profile is a test field -/

section Lift

variable {ε : ℝ} {b : Profile → ℝ}

theorem contDiffAt_radius {x : Space} (hx : radius x ≠ 0) : ContDiffAt ℝ 2 radius x := by
  have hin : ContDiff ℝ 2 fun y : Space => y 0 ^ 2 + y 1 ^ 2 := by fun_prop
  have hne : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
    rw [radius_sq]; exact pow_ne_zero 2 hx
  exact hin.contDiffAt.sqrt hne

/-- The lift `U = a b(s,q,η)` is jointly `C²` in `(x, τ)` off the axis. -/
theorem contDiffAt_liftU (hε : ε ≠ 0) {y : Space × ℝ} (hy : radius y.1 ≠ 0)
    (hb : ContDiffAt ℝ 2 b (chart ε y)) : ContDiffAt ℝ 2 (liftU ε b) y := by
  have hrad : ContDiffAt ℝ 2 (fun y : Space × ℝ => radius y.1) y :=
    (contDiffAt_radius hy).comp y contDiffAt_fst
  have hz : ContDiffAt ℝ 2 (fun y : Space × ℝ => y.1 2) y := by fun_prop
  have hG : ContDiffAt ℝ 2 (fun y : Space × ℝ => Gm ε y.2 (y.1 2) (radius y.1)) y := by
    have h1 : ContDiffAt ℝ 2 (fun y : Space × ℝ => (radius y.1 ^ 2)⁻¹) y :=
      (hrad.pow 2).inv (pow_ne_zero 2 hy)
    have h2 : ContDiffAt ℝ 2
        (fun y : Space × ℝ => ε⁻¹ * Real.log (radius y.1) + y.2 / (2 * ε)) y :=
      (contDiffAt_const.mul (hrad.log hy)).add (contDiffAt_snd.div_const _)
    have h3 : ContDiffAt ℝ 2 (fun y : Space × ℝ => y.1 2 / (ε * radius y.1)) y :=
      hz.div (contDiffAt_const.mul hrad) (mul_ne_zero hε hy)
    exact h1.prodMk (h2.prodMk h3)
  exact (hrad.inv hy).mul (hb.comp y hG)

theorem chart_fst_pos {y : Space × ℝ} (hy : radius y.1 ≠ 0) : 0 < (chart ε y).1 := by
  show 0 < (radius y.1 ^ 2)⁻¹
  have := radius_pos hy
  positivity

/-- The lift of a `C²`, `q`-periodic profile supported in `s ∈ [s₀, S₁]`, `|η| ≤ Z` is a test
field. -/
theorem isTestField_liftU {c s0 S1 Z : ℝ} (hε : 0 < ε) (hs0 : 0 < s0) (hS1 : s0 ≤ S1)
    (hb : ContDiffOn ℝ 2 b {p | 0 < p.1}) (hper : QPeriodic c b)
    (hsupp : ∀ p : Profile, 0 < p.1 → b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z) :
    IsTestField ε c (liftU ε b) where
  smooth y hy := contDiffAt_liftU hε.ne' hy
    (hb.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds (chart_fst_pos hy)))
  axis := by
    have hS1 : 0 < S1 := hs0.trans_le hS1
    refine ⟨(√S1)⁻¹, by positivity, fun y hy => ?_⟩
    by_cases h0 : radius y.1 = 0
    · simp [liftU, liftA_eq_zero h0]
    · have hr := radius_pos h0
      have hbz : b (chart ε y) = 0 := by
        by_contra hne
        have h1 := (hsupp _ (chart_fst_pos h0) hne).1.2
        have h2 : √S1 < (radius y.1)⁻¹ := (lt_inv_comm₀ hr (by positivity)).1 hy
        have h3 : (√S1) ^ 2 < ((radius y.1)⁻¹) ^ 2 := by gcongr
        rw [Real.sq_sqrt hS1.le, inv_pow] at h3
        exact absurd h1 (not_le.2 h3)
      simp [liftU, hbz]
  bounded := by
    refine ⟨√((1 + ε ^ 2 * Z ^ 2) / s0), fun y hy => ?_⟩
    by_contra hne
    have hr0 : radius y.1 ≠ 0 := by
      intro h0
      exact hne (by simp [liftU, liftA_eq_zero h0])
    have hbne : b (chart ε y) ≠ 0 := by
      intro hz
      exact hne (by simp [liftU, hz])
    obtain ⟨⟨h1, -⟩, h2⟩ := hsupp _ (chart_fst_pos hr0) hbne
    have hr := radius_pos hr0
    set r := radius y.1 with hr_def
    have h1' : r ^ 2 ≤ s0⁻¹ := (le_inv_comm₀ hs0 (by positivity)).1 h1
    have h2' : |y.1 2 / (ε * r)| ≤ Z := h2
    have hZ : 0 ≤ Z := (abs_nonneg _).trans h2'
    have h3 : |y.1 2| ≤ Z * (ε * r) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < ε * r), div_le_iff₀ (by positivity)] at h2'
      exact h2'
    have h4 : y.1 2 ^ 2 ≤ Z ^ 2 * ε ^ 2 * r ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs] at this
      nlinarith [this]
    have hnorm : ‖y.1‖ ^ 2 = r ^ 2 + y.1 2 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, hr_def, ← radius_sq]
      simp [Real.norm_eq_abs, sq_abs]
    have h5 : ‖y.1‖ ^ 2 ≤ (1 + ε ^ 2 * Z ^ 2) / s0 := by
      rw [hnorm, add_div, one_div]
      have : Z ^ 2 * ε ^ 2 * r ^ 2 ≤ ε ^ 2 * Z ^ 2 / s0 := by
        rw [div_eq_mul_inv]
        have := mul_le_mul_of_nonneg_left h1' (by positivity : 0 ≤ ε ^ 2 * Z ^ 2)
        nlinarith [this]
      linarith
    have h6 : ‖y.1‖ ≤ √((1 + ε ^ 2 * Z ^ 2) / s0) := Real.le_sqrt_of_sq_le h5
    exact absurd hy (not_lt.2 h6)
  periodic x τ := liftU_periodic hε.ne' hper x τ

end Lift

/-! ### The conjugate acts on smooth profiles by the formula `A_ε` -/

theorem jConst_ne_zero {ε : ℝ} (hε : 0 < ε) : jConst ε ≠ 0 := by
  unfold jConst
  have : √(2 * π) ≠ 0 := by positivity
  exact inv_ne_zero (mul_ne_zero this hε.ne')

section Formula

variable {ν ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)

/-- For an `H`-class `F` of a `q`-periodic profile `f`, `J_ε F = (√(2π) ε)⁻¹ a f(s,q,η)`. -/
theorem Jsc_ae_of_periodic {f : Profile → ℝ} (hf : QPeriodic c f) (F : HSpace c ℝ)
    (hF : (F : Profile → ℝ) =ᵐ[measureH c] f) :
    (Jsc hε hc F : Space × ℝ → ℝ) =ᵐ[physMeasure ε c] fun y => jConst ε * liftU ε f y := by
  have h1 := (jCompSc hε hc).coeFn_toLI F
  have h2 := (jCompSc hε hc).compFun_congr hF
  filter_upwards [h1, h2] with y hy1 hy2
  change (jCompSc hε hc).toLI F y = _
  rw [hy1, hy2]
  simp only [WeightedComp.compFun, jCompSc, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, liftU]
  have hcell : f (cellChart ε c y) = f (chart ε y) := periodic_reduceIoc_eq f hf _ _ _
  rw [hcell]
  ring

/-- **The conjugate acts on smooth profiles by `A_ε`** (tex lines 3316–3347). Let `G` be an
operator on `L²(dx dτ)` acting on test fields as the classical outer operator
(`GeneratorOnTestFields`, the property of the exact whole-space generator used here). Let `b`
be a `C²`, `c`-periodic profile supported in `s ∈ [s₀, S₁]`, `|η| ≤ Z`, with `H`-class `bL`, and
let `Ab` be the `H`-class of `A_ε b`. Then `bL` lies in the domain of `J_ε⁻¹ G J_ε` and
`J_ε⁻¹ G J_ε bL = Ab`. -/
theorem conjOp_eq_Aeps (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c)
    (hG : GeneratorOnTestFields ν ε c G) {b : Profile → ℝ} {s0 S1 Z : ℝ} (hs0 : 0 < s0)
    (hS1 : s0 ≤ S1) (hb : ContDiffOn ℝ 2 b {p | 0 < p.1}) (hper : QPeriodic c b)
    (hsupp : ∀ p : Profile, 0 < p.1 → b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z)
    (bL : HSpace c ℝ) (hbL : (bL : Profile → ℝ) =ᵐ[measureH c] b)
    (Ab : HSpace c ℝ) (hAb : (Ab : Profile → ℝ) =ᵐ[measureH c] Aeps ν ε b) :
    ∃ h : bL ∈ (conjOp hε hc G).domain, conjOp hε hc G ⟨bL, h⟩ = Ab := by
  set k := jConst ε with hk_def
  have hk : k ≠ 0 := jConst_ne_zero hε
  have hJb := Jsc_ae_of_periodic hε hc hper bL hbL
  have hJA := Jsc_ae_of_periodic hε hc (qPeriodic_Aeps ν ε hper) Ab hAb
  set V' : PhysL2sc ε c := k⁻¹ • Jsc hε hc bL with hV'_def
  have hV' : (V' : Space × ℝ → ℝ) =ᵐ[physMeasure ε c] liftU ε b := by
    filter_upwards [Lp.coeFn_smul k⁻¹ (Jsc hε hc bL), hJb] with y h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  obtain ⟨hdom, hGV⟩ := hG (liftU ε b) (isTestField_liftU hε hs0 hS1 hb hper hsupp) V' hV'
  have houter : outerGen ν ε (liftU ε b) =ᵐ[physMeasure ε c] liftU ε (Aeps ν ε b) := by
    filter_upwards [ae_physMeasure ε c] with y hy
    obtain ⟨x, τ⟩ := y
    have hbx : ContDiffAt ℝ 2 b (chart ε (x, τ)) :=
      hb.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds (chart_fst_pos hy.1))
    rw [outerGen_liftU hε.ne' hy.1 hbx]
    rfl
  have hJeq : Jsc hε hc bL = k • V' := by
    rw [hV'_def, smul_smul, mul_inv_cancel₀ hk, one_smul]
  have hdom' : Jsc hε hc bL ∈ G.domain := by
    rw [hJeq]; exact G.domain.smul_mem k hdom
  have hGeq : G ⟨Jsc hε hc bL, hdom'⟩ = k • G ⟨V', hdom⟩ := by
    rw [← LinearPMap.map_smul]
    congr 1
    exact Subtype.ext hJeq
  refine conjOp_of_eq hε hc G hdom' ?_
  rw [hGeq]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul k (G ⟨V', hdom⟩), hGV, houter, hJA] with y h1 h2 h3 h4
  rw [h1, Pi.smul_apply, h2, h3, h4, smul_eq_mul]

end Formula

end UnforcedLeray.B0221
