import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Kflat.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtCongr
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Linear
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefLinear

/-!
# The near clauses and the curved-flat comparison along the concrete return sequence
(source 5536-5547, 5640-5662, 5883-5899, 4079-4132, 5926-5950)

Source of record: `the November 2 reference manuscript` (73 pages).

For the concrete return sequence `concreteReturnSeq D G` of `Concrete/ReturnInst.lean`
(viscosities `ν_n = retNu`, amplitudes `ε_n = retEps`, `c_n = ν_n⁻²`, window
`μ_n(z) = muWin σ₀ ν_n z`, operators `B.toOps` of the pinned base `concreteBase` where the near
layer is invertible):

* `pairNormAndNearSolver_concrete` : `PairNormAndNearSolver (concreteReturnSeq D G) γ η_δ`
  (`StatementsA.lean`; source 5540-5547 with the pair norm 5657-5658), `γ = Re λ`,
  `η_δ = γ tanh(3δ/8)`;
* `curvedFlatComparison_concrete` : `CurvedFlatComparison (concreteReturnSeq D G) a_s c'`
  (source 5891-5899), `c' > 0` the exponent of the forced-column comparison (4109-4132).

## Order of choice (source 4109-4124, 5878-5881, 5922-5950)

First the reference `(λ, κ, ℓ₊(H₀), 𝒥)` with `σ₀ ∈ (0,1/4)`, the window
`K_σ₀ = [σ₀/2, σ₀/2 + 1/8] ⋐ (0,1/4)` around `σ₀` (`winK`), `m_Z > 3/2` and the regime window
`[d₋, d₊]`; then the integer `K` of `near:deltaN`; then `a, b, δ, m₀, D_⊥` (`NearChoice`:
`K(a+b) < 1/100`, `η_δ, m₀ < θd₀/8`, `D_⊥ > η_δ + θd₀`, `d₀ = γ/3`), `C₀, k₀` and the slow age
`Σ`; then the forced-column exponent `c'`; then `a_s` and the cutoff profiles; then the
backgrounds (`SeqData`).  `c'` is chosen before `a_s`, as the closing budget requires
(`1.1a_s < c_N/4`, 5878-5881).  The phase lock gives `ε_n = C_*ν_n^r e^{-(γ/3)/ν_n}`,
`C_* = (2|𝒞(σ₀)|)^{-1/3}`, `r = (Re κ - 5 - 2σ₀)/3` (`retEps_eq`, 5936-5940: the
`ε`-hypothesis of the near solver), and `ε_n³e^{γ/ν_n} = ν_n^{Re κ-5-2σ₀}/(2|𝒞(σ₀)|)`
(`retEps_cube_mul`), a viscosity polynomial.

## Hypotheses

Per-level data (pins of `SeqData`, as in `Concrete/ReturnInst.lean`): `SeqData.IsActualLevel`
for large `n` (regime, exact split, profile), the inlet support `S_in ≤ ε^{-b}` (4109-4124),
and for (b) the cutoff classes of `χ̂_f, χ̂_y` and the flat-setting pin
`Kflat.IsFlatDuhamelColumn` (4596-4610; for the actual flat setting this is task
`PartIII-b:C/flatset/col`).

Source facts taken as hypotheses, each a queued task: `NearSolverC` (`PartIII-b:C/near/6`,
`nearSolverC_of` from `C/near/3`, `C/near/delta`, `C/near/masked-bound`), `NearOpsExistC`
(`C/near/5`), `ForcedColumnC` (`C/near/forced`), `BodyRealForms` (`C/near/body-real/5`),
`SourceLInAff` (`C/srcL/15`), `FACoefBound` (`C/inst/9`) and the envelope `AffMEnvelope`
(`C/env/3`; its body is stated inline because `Concrete/AffineEnvelope.lean` cannot be imported
together with `Concrete/SourceL.lean`).  The accepted `sourceLLinear` (`C/srcL/14`),
`faCoefLinear` (`C/inst/6`) and `SourceLBounded = sourceLBounded_of sourceLAmbient sourceLN0`
(`C/srcL/9`, `C/srcL/2`) are used directly.

## Proved here

`retEps_eq`, `retEps_cube_mul`, `eventually_mu_mem` (the window), `seq_levels`;
`concreteBase_isFlatColumnKflat` (`𝒦^flat = 𝓛T₀F` for the pinned base: `𝓛 ∘ T₀ ∘ F` satisfies
the `𝒦^flat` pin by the column readout of `NearInst/Link/Kflat/Assembly.lean`, so the pinned
`𝒦^flat` exists and is it); the `F_A` family and its bound `‖F‖ ≤ P_ν e^{1.1a_s/ν}`
(`faFamily`, 5089-5091, 5893-5895); `‖𝓛‖ ≤ P_ν ε³e^{γ/ν}` (4930-4937); and the two targets.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-! ## 1. The phase-locked parameters (source 5936-5946) -/

/-- `C_* = (2|𝒞(σ₀)|)^{-1/3}` (source 5936-5940). -/
def epsCst (Pl : PlanarData) (σ₀ : ℝ) : ℝ := ((2 * ‖Pl.signedCoeff σ₀‖) ^ (1 / 3 : ℝ))⁻¹

/-- `r = (Re κ - 5 - 2σ₀)/3` (source 5936-5940). -/
def epsPow (Pl : PlanarData) (σ₀ : ℝ) : ℝ := (Pl.kappa.re - 5 - 2 * σ₀) / 3

theorem epsCst_pos {Pl : PlanarData} {σ₀ : ℝ} (h : Pl.signedCoeff σ₀ ≠ 0) : 0 < epsCst Pl σ₀ :=
  inv_pos.2 (Real.rpow_pos_of_pos (mul_pos two_pos (norm_pos_iff.2 h)) _)

/-- **`ε_n = C_* ν_n^r e^{-(γ/3)/ν_n}`** (source 5936-5940; the `ε`-hypothesis of the near solver,
4109-4124, with `d₀ = γ/3`). -/
theorem retEps_eq {Pl : PlanarData} {σ₀ : ℝ} (h : Pl.signedCoeff σ₀ ≠ 0) (n : ℕ) :
    retEps Pl σ₀ n = epsCst Pl σ₀ * retNu Pl σ₀ n ^ epsPow Pl σ₀ *
      Real.exp (-(Pl.eigenvalue.re / 3) / retNu Pl σ₀ n) := by
  have hν := retNu_pos Pl σ₀ n
  have hc : 0 < 2 * ‖Pl.signedCoeff σ₀‖ := mul_pos two_pos (norm_pos_iff.2 h)
  have ha : 0 ≤ Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) := (Real.exp_pos _).le
  have hb : 0 ≤ retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) := Real.rpow_nonneg hν.le _
  unfold retEps epsCst epsPow
  rw [Real.div_rpow (mul_nonneg ha hb) hc.le, Real.mul_rpow ha hb, ← Real.exp_mul,
    ← Real.rpow_mul hν.le]
  have e1 : -(Pl.eigenvalue.re / retNu Pl σ₀ n) * (1 / 3) =
      -(Pl.eigenvalue.re / 3) / retNu Pl σ₀ n := by ring
  have e2 : (Pl.kappa.re - 5 - 2 * σ₀) * (1 / 3) = (Pl.kappa.re - 5 - 2 * σ₀) / 3 := by ring
  rw [e1, e2, div_eq_mul_inv]
  ring

/-- **`ε_n³e^{γ/ν_n} = ν_n^{Re κ - 5 - 2σ₀}/(2|𝒞(σ₀)|)`** (source 5936-5940): on the
phase-locked sequence the factor `ε³e^{γ/ν}` of the `𝓛` bound (4930-4937) is polynomial. -/
theorem retEps_cube_mul {Pl : PlanarData} {σ₀ : ℝ} (h : Pl.signedCoeff σ₀ ≠ 0) (n : ℕ) :
    retEps Pl σ₀ n ^ 3 * Real.exp (Pl.eigenvalue.re / retNu Pl σ₀ n) =
      retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) / (2 * ‖Pl.signedCoeff σ₀‖) := by
  have hν := retNu_pos Pl σ₀ n
  have hc : 0 < 2 * ‖Pl.signedCoeff σ₀‖ := mul_pos two_pos (norm_pos_iff.2 h)
  have hx : 0 ≤ Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) *
      retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) / (2 * ‖Pl.signedCoeff σ₀‖) :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hν.le _)) hc.le
  have h3 : retEps Pl σ₀ n ^ 3 = Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) *
      retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) / (2 * ‖Pl.signedCoeff σ₀‖) := by
    unfold retEps
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have he : Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) *
      Real.exp (Pl.eigenvalue.re / retNu Pl σ₀ n) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [h3]
  calc Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) *
        retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) / (2 * ‖Pl.signedCoeff σ₀‖) *
        Real.exp (Pl.eigenvalue.re / retNu Pl σ₀ n)
      = (Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) *
          Real.exp (Pl.eigenvalue.re / retNu Pl σ₀ n)) *
          (retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) / (2 * ‖Pl.signedCoeff σ₀‖)) := by ring
    _ = _ := by rw [he, one_mul]

/-- For `0 < ν ≤ 1`, `ν^r ≤ ν^{-k}`, `k = ⌈-r⌉₊`. -/
theorem seq_rpow_le_inv_pow {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (r : ℝ) :
    ν ^ r ≤ ν⁻¹ ^ (⌈-r⌉₊) := by
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hν.le]
  exact Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith [Nat.le_ceil (-r)])

/-- The phase-locked amplitude in the form of the near solver (source 4109-4124, 5936-5940):
`ε_n = C ν_n^r e^{-(γ/3)/ν_n}` with `C ∈ [C_*, C_*]`, `r ∈ [-|r_*|, |r_*|]`. -/
theorem seq_epsForm (D : SeqData) (n : ℕ) :
    ∃ Cs ∈ Icc (epsCst D.Pl D.σ₀) (epsCst D.Pl D.σ₀),
      ∃ r ∈ Icc (-|epsPow D.Pl D.σ₀|) |epsPow D.Pl D.σ₀|,
        ((D.level n).params D.Pl).ε = Cs * ((D.level n).params D.Pl).ν ^ r *
          Real.exp (-(D.Pl.eigenvalue.re / 3) / ((D.level n).params D.Pl).ν) :=
  ⟨_, ⟨le_rfl, le_rfl⟩, _, ⟨neg_abs_le _, le_abs_self _⟩, retEps_eq D.coeff_ne n⟩

/-! ## 2. The window (source 5926-5927, 5946) -/

/-- The compact window `K_σ₀ = [σ₀/2, σ₀/2 + 1/8]` around `σ₀` (source 5926-5927: "fix a compact
interval `K ⋐ (0,1/4)` around it"). -/
def winK (σ₀ : ℝ) : Set ℝ := Icc (σ₀ / 2) (σ₀ / 2 + 1 / 8)

theorem isCompact_winK (σ₀ : ℝ) : IsCompact (winK σ₀) := isCompact_Icc

theorem winK_sub {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1 / 4) : winK σ₀ ⊆ Ioo 0 (1 / 4) :=
  fun _ hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- For large `n` the window `μ_n(z) = σ₀ + z/(2|log ν_n|)`, `|z| ≤ 1`, lies in `K_σ₀`
(source 5946). -/
theorem eventually_mu_mem (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0) (h0 : 0 < D.σ₀)
    (h1 : D.σ₀ < 1 / 4) : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ winK D.σ₀ := by
  set η : ℝ := min (D.σ₀ / 2) (1 / 8 - D.σ₀ / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hM : 0 < 1 / (2 * η) := by positivity
  filter_upwards [(retNu_tendsto D.σ₀ hω).eventually
    (gt_mem_nhds (Real.exp_pos (-(1 / (2 * η)))))] with n hn z hz
  have hν := retNu_pos D.Pl D.σ₀ n
  have hlog : Real.log (retNu D.Pl D.σ₀ n) < -(1 / (2 * η)) := by
    have := Real.log_lt_log hν hn
    rwa [Real.log_exp] at this
  have habs : 1 / (2 * η) < |Real.log (retNu D.Pl D.σ₀ n)| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hpos : 0 < 2 * |Real.log (retNu D.Pl D.σ₀ n)| := by linarith
  have hlt : 1 < |Real.log (retNu D.Pl D.σ₀ n)| * (2 * η) :=
    (div_lt_iff₀ (by positivity)).1 habs
  have hcomm : |Real.log (retNu D.Pl D.σ₀ n)| * (2 * η) =
      η * (2 * |Real.log (retNu D.Pl D.σ₀ n)|) := by ring
  have hz1 : |z| ≤ 1 := abs_le.2 ⟨hz.1, hz.2⟩
  have hq : |z / (2 * |Real.log (retNu D.Pl D.σ₀ n)|)| ≤ η := by
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    linarith
  obtain ⟨hq1, hq2⟩ := abs_le.1 hq
  have hηa : η ≤ D.σ₀ / 2 := min_le_left _ _
  have hηb : η ≤ 1 / 8 - D.σ₀ / 2 := min_le_right _ _
  show muWin D.σ₀ (retNu D.Pl D.σ₀ n) z ∈ Icc (D.σ₀ / 2) (D.σ₀ / 2 + 1 / 8)
  unfold muWin
  constructor <;> linarith

/-! ## 3. The parameter choice and the levels (source 4109-4124, 2031-2037, 2664-2713) -/

/-- **The parameter choice of the near layer** (source 4109-4124) for an integer `K` (the integer
of `near:deltaN`, chosen before `a, b`): there are `a > 0` and `D_⊥` with `0 < b < 1`,
`K(a+b) < 1/100`, `δ > 0`, `0 < m₀ < 3d₋/11`, `η_δ < θd₀/8`, `m₀ < θd₀/8`,
`η_δ + θd₀ < D_⊥` (`θ = min{a/2, b/2, 1/100, 3/22}`, `d₀ = γ/3`, `η_δ = γ tanh(3δ/8)`), and
`C₀ > 0` (the constant of `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`, 2706-2713). -/
def NearChoice (K : ℕ) (γ dm b δ m0 C0 : ℝ) : Prop :=
  ∃ a Dp : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ (K : ℝ) * (a + b) < 1 / 100 ∧ 0 < δ ∧ 0 < m0 ∧
    m0 < 3 * dm / 11 ∧ etaDelta γ δ < thetaAB a b * (γ / 3) / 8 ∧
    m0 < thetaAB a b * (γ / 3) / 8 ∧ etaDelta γ δ + thetaAB a b * (γ / 3) < Dp ∧ 0 < C0

/-- A smaller integer keeps `K(a+b) < 1/100`. -/
theorem seq_nat_mul_lt {K K' : ℕ} {x : ℝ} (hx : 0 ≤ x) (hK : K' ≤ K)
    (h : (K : ℝ) * x < 1 / 100) : (K' : ℝ) * x < 1 / 100 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hx) h

/-- At all large levels: the level is actual, the inlet support is below the output cut, `ν_n` is
below a given threshold and below `1`, and the window lies in `K_σ₀` (source 2031-2037,
2664-2713, 4109-4124, 5926-5950). -/
theorem seq_levels (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0) (h0 : 0 < D.σ₀)
    (h1 : D.σ₀ < 1 / 4) {dm dp : ℝ} (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n)
    (hSin : ∀ᶠ n : ℕ in atTop, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)) {ν₀ : ℝ}
    (hν₀ : 0 < ν₀) :
    ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n ∧
      D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b) ∧ retNu D.Pl D.σ₀ n ≤ ν₀ ∧
      retNu D.Pl D.σ₀ n ≤ 1 ∧ ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ winK D.σ₀ :=
  hact.and (hSin.and (((retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀)).and
    (((retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds one_pos)).and
      (eventually_mu_mem D hω h0 h1))))

/-! ## 4. (a) The near clauses along the sequence (source 5536-5547, 5657-5658) -/

/-- **`PairNormAndNearSolver` for the concrete return sequence** (source 5540-5547, 5657-5658):
`‖D_N⁻¹T‖ ≤ P_ν‖T‖`, `‖S_N T‖ ≤ P_ν e^{η_δ/ν}‖T‖` in the gain norms and the pair norm
`‖V‖ = ‖T‖ + e^{-γ/(8ν)}‖w‖` of `𝓔_ν`, `γ = Re λ`, `η_δ = γ tanh(3δ/8)`, for every background
datum whose near choices satisfy the parameter choice (`NearChoice`) for the integer of the near
solver (chosen after the reference, the window `K_σ₀`, `m_Z` and `[d₋, d₊]`), whose levels are
actual for large `n` and whose inlet supports are below the output cut `ε_n^{-b}`.  At large levels
the actual near operators exist (`NearOpsExistC`), `D_N` is a unit (`NearSolverC`), so the
operators of the sequence are those of the pinned base, which is linked to the near operators
(`concreteBase_isNearLinked`); `nearClausesC_of` gives the bounds. -/
theorem pairNormAndNearSolver_concrete (hNS : NearSolverC) (hEx : NearOpsExistC)
    (Pl : PlanarData) (hP : IsPlanarReference Pl) (hω : Pl.eigenvalue.im ≠ 0) (σ₀ : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1 / 4) (mZ : ℝ) (hmZ : 3 / 2 < mZ) (dm dp : ℝ)
    (hdm : 0 < dm) :
    ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
      NearChoice Kint (gRate Pl) dm D.K.b D.K.δ D.K.m0 D.K.C0 →
      (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
      (∀ᶠ n : ℕ in atTop, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)) →
      ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
        PairNormAndNearSolver (concreteReturnSeq D G) (gRate D.Pl)
          (etaDelta (gRate D.Pl) D.K.δ) := by
  obtain ⟨K₁, hK₁⟩ := hNS Pl hP (winK σ₀) (isCompact_winK σ₀) (winK_sub hσ₀ hσ₁) mZ hmZ dm dp hdm
  obtain ⟨K₂, hK₂⟩ := nearClausesC_of hNS Pl hP (winK σ₀) (isCompact_winK σ₀)
    (winK_sub hσ₀ hσ₁) mZ hmZ dm dp hdm
  refine ⟨max K₁ K₂, ?_⟩
  rintro D rfl rfl rfl ⟨a, Dp, ha, hb, hb1, hKab, hδ, hm0, hm0d, hη, hm0θ, hDp, hC0⟩ hact hSin G
  have hab : 0 ≤ a + D.K.b := by linarith
  obtain ⟨C₁, k₁, ν₁, hν₁, hS₁⟩ := hK₁ a D.K.b D.K.δ D.K.m0 Dp ha hb hb1
    (seq_nat_mul_lt hab (le_max_left _ _) hKab) hδ hm0 hm0d hη hm0θ hDp D.K.C0 D.K.k0 hC0
    (epsCst D.Pl D.σ₀) (epsCst D.Pl D.σ₀) |epsPow D.Pl D.σ₀| (epsCst_pos D.coeff_ne) le_rfl
    (abs_nonneg _) D.Sig D.Sig_pos
  obtain ⟨C₂, k₂, ν₂, hν₂, hS₂⟩ := hK₂ a D.K.b D.K.δ D.K.m0 Dp ha hb hb1
    (seq_nat_mul_lt hab (le_max_right _ _) hKab) hδ hm0 hm0d hη hm0θ hDp D.K.C0 D.K.k0 hC0
    (epsCst D.Pl D.σ₀) (epsCst D.Pl D.σ₀) |epsPow D.Pl D.σ₀| (epsCst_pos D.coeff_ne) le_rfl
    (abs_nonneg _) D.Sig D.Sig_pos
  obtain ⟨ν₃, hν₃, hE⟩ := hEx D.Pl hP (winK D.σ₀) (isCompact_winK _) (winK_sub hσ₀ hσ₁) D.K.mZ
    hmZ dm dp hdm D.K.b D.K.δ D.K.m0 hb hb1 hδ hm0 hm0d.le D.K.C0 D.K.k0 hC0 D.Sig D.Sig_pos
  have hν₀ : 0 < min ν₁ (min ν₂ ν₃) := lt_min hν₁ (lt_min hν₂ hν₃)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (seq_levels D hω hσ₀ hσ₁ hact hSin hν₀)
  refine ⟨C₂, k₂, N, fun n hn z hz => ?_⟩
  obtain ⟨hL, hSn, hνn, -, hμ⟩ := hN n hn
  have hn1 : retNu D.Pl D.σ₀ n ≤ ν₁ := hνn.trans (min_le_left _ _)
  have hn2 : retNu D.Pl D.σ₀ n ≤ ν₂ := hνn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hn3 : retNu D.Pl D.σ₀ n ≤ ν₃ := hνn.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hex : ∃ o : NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z) D.K.δ
        ((D.level n).Scut D.K) o :=
    hE _ _ hL.regime hn3 rfl rfl _ _ _ hL.split _ (hμ z hz)
  have hnear : NearAt D.Pl D.K (D.level n) (D.mu n z) := nearAt_of hex fun o ho =>
    (hS₁ _ _ hL.regime hn1 rfl rfl (seq_epsForm D n) _ _ _ hL.split hSn _ (hμ z hz) o ho).2.1
  obtain ⟨h1, h2, -⟩ := hS₂ _ _ hL.regime hn2 rfl rfl (seq_epsForm D n) _ _ _ hL.split hSn _
    (hμ z hz) _ (nearOpsAt_spec hex).1 (AffSp D.K.as)
    (concreteBase D.Pl D.K (D.level n) (D.mu n z) hnear) (concreteBase_isNearLinked hnear)
  refine ⟨fun T => ?_, fun T => ?_, fun V => concreteReturnSeq_pairNorm D G n z hnear V⟩
  · rw [concreteReturnSeq_ops_eq D G n z hnear]
    exact h1 T
  · rw [concreteReturnSeq_ops_eq D G n z hnear]
    exact h2 T

/-! ## 5. The pinned base: `𝒦^flat = 𝓛T₀F`, the `F_A` family, `‖𝓛‖` -/

/-- **`𝒦^flat = 𝓛T₀F` for the pinned base of a regime** (source 4761-4763, 4804-4806, 4109-4111,
5897-5899): with the `𝓛` pin of `LjOp` and the `F_A` pin of `FAOp`, the composite
`𝓛 ∘ T₀ ∘ F` (`T₀ = flatColG R₀`) satisfies the `𝒦^flat` pin `ι(𝒦A) = 𝓛(𝔗(ιA))`: the flat
column readout of `NearInst/Link/Kflat/Assembly.lean` (`IsFlatDuhamelColumn`, `IsFlatMult`,
`flatColumn_solves`, `thinFlatColG`, `srcCoefAE`, `xmtCongr`, `oldMeasureAC`).  Hence the pinned
`𝒦^flat` exists and equals it (`ι` is injective). -/
theorem concreteBase_isFlatColumnKflat {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel}
    {μ : ℝ} (h : NearAt Pl K L μ) (R0 : Hsp (cOf L.ν) →L[ℝ] Hsp (cOf L.ν))
    (hLj : ∀ T, affIota K.as (LjOp Pl K L μ T) =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
    (hFA : ∀ A, (FAOp K L μ A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      FAcoef L.ν μ K.χf (affIota K.as A))
    (hχf : IsSourceCutoffC K.χf)
    (hM0 : IsFlatMult (nearOpsAt Pl K L μ).M0 L.train)
    (hS0 : IsFreeStress (nearOpsAt Pl K L μ).S0 L.ν μ)
    (hR0 : IsBodyTransport R0
      (UnforcedLeray.Short.PartIIa.T0flat (cOf_pos L.ν_pos) L.ν (μ : ℂ)))
    (hD0 : IsUnit (nearOpsAt Pl K L μ).D0)
    (hS : Kflat.IsFlatDuhamelColumn L.flat (cOf_pos L.ν_pos) L.train μ K.as K.χf) :
    IsFlatColumnKflat (concreteBase Pl K L μ h) (nearOpsAt Pl K L μ) R0 L.ν_pos := by
  set o := nearOpsAt Pl K L μ with ho
  set X : AffSp K.as →L[ℝ] AffSp K.as :=
    LjOp Pl K L μ ∘L o.flatColG (gRate Pl) L.ν_pos R0 ∘L FAOp K L μ with hXdef
  have hX : ∀ A, affIota K.as (X A) =
      KflatFun L.flat (cOf L.ν) L.ν L.ε μ K.χo K.χy K.χf (affIota K.as A) := by
    intro A
    rw [hXdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hLj]
    symm
    unfold KflatFun LjFun
    apply Lpt_congr_Xmt
    apply xmtCongr (cOf L.ν) L.ν L.ε μ K.χo K.χy K.hχo L.ν_pos
    set hh : Hsp (cOf L.ν) := (Real.sqrt Real.pi)⁻¹ • srcIso (cOf L.ν) (FAOp K L μ A)
      with hh_def
    have hhae : (hh : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)]
        Kflat.affCoef L.ν μ K.χf (affIota K.as A) :=
      Kflat.srcCoefAE (cOf L.ν) (FAOp K L μ A) _ (hFA A)
    obtain ⟨hMb, hb⟩ := Kflat.flatColumn_solves o R0 hD0 hh
    set b : Hsp (cOf L.ν) := R0 hh - o.S0 (Ring.inverse o.D0 (o.M0 (R0 hh))) with hb_def
    have h1 := hS hχf K.mZ (L.ρb Pl K) o R0 hM0 hS0 hR0 hD0 (affIota K.as A)
      (affIota_mem K.as A) hh b hhae hb
    have h2 : (((Ring.inverse o.D0 (o.M0 (R0 hh))).fst : Chart → Ten3)) =ᵐ[z1Measure (cOf L.ν) K.mZ]
        fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter (trainMer L.train p) (b p)) := by
      rw [← hMb]
      exact (hM0 b).1
    have h2' := (oldMeasureAC (cOf L.ν) K.mZ (gRate Pl) L.ν L.ν_pos).ae_le
      ((withDensity_absolutelyContinuous (z1Measure (cOf L.ν) K.mZ) _).ae_le h2)
    have h3 := (oldMeasureAC (cOf L.ν) K.mZ (gRate Pl) L.ν L.ν_pos).ae_le
      (Kflat.thinFlatColG (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ν_pos o R0
        (FAOp K L μ A))
    filter_upwards [h1, h2', h3] with p hp1 hp2 hp3
    rw [hp1, hp3, hp2]
    rfl
  have hKf : ∀ A, affIota K.as (KflatOp K L μ A) =
      KflatFun L.flat (cOf L.ν) L.ν L.ε μ K.χo K.χy K.χf (affIota K.as A) :=
    Classical.epsilon_spec (p := fun Kf : AffSp K.as →L[ℝ] AffSp K.as => ∀ A,
      affIota K.as (Kf A) =
        KflatFun L.flat (cOf L.ν) L.ν L.ε μ K.χo K.χy K.χf (affIota K.as A)) ⟨X, hX⟩
  show KflatOp K L μ = X
  ext1 A
  exact affIota_injective K.as ((hKf A).trans (hX A).symm)

/-- **The `F_A` family of a regime** (source 4981, 4985, 5009-5016, 5089-5091): `A ↦ F_A` is an
`L²` family on `𝒜` for the ungained body measure, from the linearity of `F_A` (`FACoefLinear`),
the first line of `ret:general-affine-bounds` for `F_A` at `(ν, μ)` and an envelope
`M(ιA) ≤ C_env‖A‖`. -/
theorem faFamily {as ν μ : ℝ} {χf : ℝ → ℝ} (hν : 0 < ν) (lF : FACoefLinear as χf) (C : ℝ)
    (k : ℕ) (hC : 0 ≤ C)
    (bF : ∀ A : ℝ → Mat3, IsAffElem as A → MemLp (FAcoef ν μ χf A) 2 (srcMeasure (cOf ν)) ∧
      eLpNorm (FAcoef ν μ χf A) 2 (srcMeasure (cOf ν)) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * affM ν χf A))
    (Cenv : ℝ) (henv : ∀ A : AffSp as, affM ν χf (affIota as A) ≤ Cenv * ‖A‖) :
    IsL2Family (srcMeasure (cOf ν)) fun A : AffSp as => FAcoef ν μ χf (affIota as A) := by
  have hsrc : ∀ᵐ p ∂(srcMeasure (cOf ν)), 0 < p.1 := ae_srcMeasure_fst_pos _
  have hCk : 0 ≤ C * ν⁻¹ ^ k := mul_nonneg hC (pow_nonneg (inv_nonneg.2 hν.le) _)
  exact
    { memLp := fun A => (bF _ (affIota_mem as A)).1
      add := fun A A' => by
        filter_upwards [hsrc] with p hp
        simp only [map_add, Pi.add_apply]
        exact (lF ν μ hν _ _ 1 (affIota_mem as A) (affIota_mem as A') p hp).1
      smul := fun r A => by
        filter_upwards [hsrc] with p hp
        simp only [map_smul, Pi.smul_apply]
        exact (lF ν μ hν _ _ r (affIota_mem as A) (affIota_mem as A) p hp).2
      bound := ⟨C * ν⁻¹ ^ k * Cenv, fun A => (bF _ (affIota_mem as A)).2.trans
        (ENNReal.ofReal_le_ofReal (by
          calc C * ν⁻¹ ^ k * affM ν χf (affIota as A) ≤ C * ν⁻¹ ^ k * (Cenv * ‖A‖) :=
                mul_le_mul_of_nonneg_left (henv A) hCk
            _ = C * ν⁻¹ ^ k * Cenv * ‖A‖ := by ring))⟩ }

/-! ## 6. (b) The curved loop against the flat return along the sequence (source 5891-5899) -/

set_option maxRecDepth 20000 in
/-- **`CurvedFlatComparison` for the concrete return sequence** (source 5883-5899):
`‖L𝒫 - 𝒦^flat‖ ≤ P_ν e^{-(c' - 1.1a_s)/ν}` with `c' > 0` the exponent of the forced-column
comparison (4109-4132), chosen after the near choices `(b, δ, m₀, C₀, k₀, Σ)` and before `a_s`,
the cutoff profiles and the backgrounds.  At large levels the base is the pinned one, linked to
the near operators and to the curved body inverse; `curvedFlat_le` with
`𝒦^flat = 𝓛T₀F` (`concreteBase_isFlatColumnKflat`), the column bound of `BodyColumnC`
(`bodyColumnC_of`, no gain on the input, 4116-4118), `‖𝓛‖ ≤ P_ν ε³e^{γ/ν} = P_ν`
(`SourceLBounded`, 4930-4937, polynomial on the phase lock, 5883-5890) and
`‖F‖ ≤ P_ν e^{1.1a_s/ν}` (the first line of `ret:general-affine-bounds` for `F_A` with the
generic envelope `M(A) ≤ Ce^{1.1a_s/ν}‖A‖_𝒜`, 5089-5091, 5893-5895). -/
theorem curvedFlatComparison_concrete (hNS : NearSolverC) (hEx : NearOpsExistC)
    (hFC : ForcedColumnC) (hBR : BodyRealForms)
    (hIn : ∀ (as c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ), SourceLInAff as c mZ ρb γ ν ε μ χo χy)
    (hFb : ∀ (as : ℝ) (χf : ℝ → ℝ), IsSourceCutoffC χf → FACoefBound as χf)
    (hEnv : ∀ χ : ℝ → ℝ, IsSourceCutoffC χ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (as ν : ℝ) (A : ℝ → Mat3),
      0 ≤ as → 0 < ν → IsAffElem as A → affM ν χ A ≤ C * Real.exp (1.1 * as / ν) * affNorm as A)
    (Pl : PlanarData) (hP : IsPlanarReference Pl) (hω : Pl.eigenvalue.im ≠ 0) (σ₀ : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1 / 4) (hCσ : Pl.signedCoeff σ₀ ≠ 0) (mZ : ℝ) (hmZ : 3 / 2 < mZ)
    (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ Kint : ℕ, ∀ (b δ m0 C0 : ℝ) (k0 : ℕ) (Sig : ℝ),
      NearChoice Kint (gRate Pl) dm b δ m0 C0 → 0 < Sig →
      ∃ c' : ℝ, 0 < c' ∧ ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.K.b = b →
        D.K.δ = δ → D.K.m0 = m0 → D.K.C0 = C0 → D.K.k0 = k0 → D.Sig = Sig →
        0 < D.K.as → IsSourceCutoffC D.K.χf → IsStreamCutoff D.K.χy →
        (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
        (∀ᶠ n : ℕ in atTop, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)) →
        (∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, Kflat.IsFlatDuhamelColumn (D.flat n)
          (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf) →
        ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
          CurvedFlatComparison (concreteReturnSeq D G) D.K.as c' := by
  have hγ : 0 < gRate Pl := hP.eigenpair.re_pos
  obtain ⟨K₁, hK₁⟩ := hNS Pl hP (winK σ₀) (isCompact_winK σ₀) (winK_sub hσ₀ hσ₁) mZ hmZ dm dp hdm
  obtain ⟨K₂, hK₂⟩ := bodyColumnC_of hFC Pl hP (winK σ₀) (isCompact_winK σ₀)
    (winK_sub hσ₀ hσ₁) mZ hmZ dm dp hdm
  obtain ⟨ν₄, hν₄, hBR'⟩ := hBR (winK σ₀) (isCompact_winK σ₀) (winK_sub hσ₀ hσ₁) dm dp hdm
  refine ⟨max K₁ K₂, fun b δ m0 C0 k0 Sig hch hSig => ?_⟩
  obtain ⟨a, Dp, ha, hb, hb1, hKab, hδ, hm0, hm0d, hη, hm0θ, hDp, hC0⟩ := hch
  have hab : 0 ≤ a + b := by linarith
  obtain ⟨C₁, k₁, ν₁, hν₁, hS₁⟩ := hK₁ a b δ m0 Dp ha hb hb1
    (seq_nat_mul_lt hab (le_max_left _ _) hKab) hδ hm0 hm0d hη hm0θ hDp C0 k0 hC0
    (epsCst Pl σ₀) (epsCst Pl σ₀) |epsPow Pl σ₀| (epsCst_pos hCσ) le_rfl (abs_nonneg _) Sig hSig
  obtain ⟨c', C₂, k₂, ν₂, hc', hν₂, hS₂⟩ := hK₂ a b δ m0 Dp ha hb hb1
    (seq_nat_mul_lt hab (le_max_right _ _) hKab) hδ hm0 hm0d hη hm0θ hDp C0 k0 hC0
    (epsCst Pl σ₀) (epsCst Pl σ₀) |epsPow Pl σ₀| (epsCst_pos hCσ) le_rfl (abs_nonneg _) Sig hSig
  obtain ⟨ν₃, hν₃, hE⟩ := hEx Pl hP (winK σ₀) (isCompact_winK _) (winK_sub hσ₀ hσ₁) mZ hmZ dm dp
    hdm b δ m0 hb hb1 hδ hm0 hm0d.le C0 k0 hC0 Sig hSig
  refine ⟨c', hc', ?_⟩
  rintro D rfl rfl rfl rfl rfl rfl rfl rfl rfl has hχf hχy hact hSin hflat G
  refine ⟨hc', ?_⟩
  have hBd : ∀ (as mZ γ : ℝ) (Kset : Set ℝ) (χo χy : ℝ → ℝ), SourceLBounded as mZ γ Kset χo χy :=
    fun as mZ γ Kset χo χy => sourceLBounded_of (sourceLAmbient as Kset χo χy) (sourceLN0 mZ γ)
  obtain ⟨CL, kL, hCL⟩ := hBd D.K.as D.K.mZ (gRate D.Pl) (winK D.σ₀) D.K.χo D.K.χy has
    (isCompact_winK _) (winK_sub hσ₀ hσ₁) hmZ hγ
  obtain ⟨CF, kF, hCF0, hCF⟩ := hFb D.K.as D.K.χf hχf (winK D.σ₀) (isCompact_winK _)
    (winK_sub hσ₀ hσ₁)
  obtain ⟨Ce, hCe0, hCe⟩ := hEnv D.K.χf hχf
  set k₄ : ℕ := ⌈-(D.Pl.kappa.re - 5 - 2 * D.σ₀)⌉₊ with hk₄
  have hν₀ : 0 < min ν₁ (min ν₂ (min ν₃ ν₄)) := lt_min hν₁ (lt_min hν₂ (lt_min hν₃ hν₄))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((seq_levels D hω hσ₀ hσ₁ hact hSin hν₀).and hflat)
  refine ⟨|CL| / (2 * ‖D.Pl.signedCoeff D.σ₀‖) * |C₂| * CF * Ce, kL + k₄ + k₂ + kF, N,
    fun n hn z hz => ?_⟩
  obtain ⟨⟨hL, hSn, hνn, hν1, hμ⟩, hfl⟩ := hN n hn
  have hn1 : retNu D.Pl D.σ₀ n ≤ ν₁ := hνn.trans (min_le_left _ _)
  have hn2 : retNu D.Pl D.σ₀ n ≤ ν₂ := hνn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hn3 : retNu D.Pl D.σ₀ n ≤ ν₃ :=
    hνn.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hn4 : retNu D.Pl D.σ₀ n ≤ ν₄ :=
    hνn.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hμK : D.mu n z ∈ winK D.σ₀ := hμ z hz
  have hμI : D.mu n z ∈ Ioo (0 : ℝ) (1 / 4) := winK_sub hσ₀ hσ₁ hμK
  have hνp : 0 < retNu D.Pl D.σ₀ n := retNu_pos D.Pl D.σ₀ n
  -- the near layer
  have hex : ∃ o : NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z) D.K.δ
        ((D.level n).Scut D.K) o :=
    hE _ _ hL.regime hn3 rfl rfl _ _ _ hL.split _ hμK
  have hAN := (nearOpsAt_spec hex).1
  have hNSl := hS₁ _ _ hL.regime hn1 rfl rfl (seq_epsForm D n) _ _ _ hL.split hSn _ hμK _ hAN
  have hnear : NearAt D.Pl D.K (D.level n) (D.mu n z) := nearAt_of hex fun o ho =>
    (hS₁ _ _ hL.regime hn1 rfl rfl (seq_epsForm D n) _ _ _ hL.split hSn _ hμK o ho).2.1
  -- the body inverses
  obtain ⟨hTe, R0, hR0⟩ := hBR' _ _ hL.regime hn4 _ hμK
  have hReps := Classical.epsilon_spec hTe
  -- the column bound
  have hcol := hS₂ _ _ hL.regime hn2 rfl rfl (seq_epsForm D n) _ _ _ hL.split hSn _ hμK _ hAN _ R0
    hReps hR0 (AffSp D.K.as) (concreteBase D.Pl D.K (D.level n) (D.mu n z) hnear)
    (concreteBase_isNearLinked hnear) (concreteBase_isBodyLinked hnear)
  -- the `𝓛` pin and bound
  have hLH : LHyp (cOf (retNu D.Pl D.σ₀ n)) (retNu D.Pl D.σ₀ n) (retEps D.Pl D.σ₀ n) (D.mu n z)
      D.K.χo D.K.χy :=
    ⟨cOf_pos hνp, hνp, hν1, retEps_pos D.coeff_ne n, hμI.1, hμI.2, D.K.hχo, hχy⟩
  have hLjex := exists_LjOp_of (Pl := D.Pl) (K := D.K) (L := D.level n) (μ := D.mu n z) hLH hmZ
    hγ has (Set.singleton_subset_iff.2 hμI) (hIn _ _ _ _ _ _ _ _ _ _) (sourceLLinear _ _ _ _ _ _ _ _ _)
    (hBd _ _ _ _ _ _)
  have hLj : ∀ T, affIota D.K.as (LjOp D.Pl D.K (D.level n) (D.mu n z) T) =
      LjFun (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
        (D.level n).ε (D.mu n z) D.K.χo D.K.χy T :=
    Classical.epsilon_spec hLjex
  set X : ℝ := retEps D.Pl D.σ₀ n ^ 3 * Real.exp (gRate D.Pl / retNu D.Pl D.σ₀ n) with hXdef
  have hX0 : 0 ≤ X := mul_nonneg (pow_nonneg (retEps_pos D.coeff_ne n).le 3) (Real.exp_pos _).le
  have hνi : 0 ≤ (retNu D.Pl D.σ₀ n)⁻¹ := inv_nonneg.2 hνp.le
  have hLnorm : ‖LjOp D.Pl D.K (D.level n) (D.mu n z)‖ ≤
      |CL| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kL * X := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hνi _)) hX0) fun T => ?_
    rw [← affNorm_affIota, hLj]
    refine (hCL _ _ _ _ _ hLH hμK T).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hνi _)) hX0) (norm_nonneg _)
  -- the `F_A` family, pin and bound
  have hCFn := hCF (retNu D.Pl D.σ₀ n) (D.mu n z) hνp hν1 hμK
  have henvn : ∀ A : AffSp D.K.as, affM (retNu D.Pl D.σ₀ n) D.K.χf (affIota D.K.as A) ≤
      (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) * ‖A‖ := by
    intro A
    have h := hCe D.K.as (retNu D.Pl D.σ₀ n) (affIota D.K.as A) has.le hνp (affIota_mem _ A)
    rwa [affNorm_affIota] at h
  have hfam := faFamily (μ := D.mu n z) hνp (faCoefLinear D.K.as D.K.χf hχf) CF kF hCF0 hCFn _ henvn
  have hFApin : ∀ A, (FAOp D.K (D.level n) (D.mu n z) A : Chart → Merid)
      =ᵐ[srcMeasure (cOf (D.level n).ν)] FAcoef (D.level n).ν (D.mu n z) D.K.χf
        (affIota D.K.as A) :=
    FAOp_spec (K := D.K) (L := D.level n) (μ := D.mu n z) ⟨hfam.toCLM, hfam.toCLM_ae⟩
  have hCe' : 0 ≤ Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n) :=
    mul_nonneg hCe0 (Real.exp_pos _).le
  have hFnorm : ‖FAOp D.K (D.level n) (D.mu n z)‖ ≤
      CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF * (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hCF0 (pow_nonneg hνi _)) hCe') fun A => ?_
    rw [Lp.norm_def, eLpNorm_congr_ae (hFApin A)]
    refine ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (mul_nonneg (mul_nonneg hCF0 (pow_nonneg hνi _)) hCe') (norm_nonneg _))
      ((hCFn _ (affIota_mem _ A)).2.trans (ENNReal.ofReal_le_ofReal ?_))
    calc CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF * affM (retNu D.Pl D.σ₀ n) D.K.χf (affIota D.K.as A)
        ≤ CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF *
            ((Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) * ‖A‖) :=
          mul_le_mul_of_nonneg_left (henvn A) (mul_nonneg hCF0 (pow_nonneg hνi _))
      _ = _ := by ring
  -- `𝒦^flat = 𝓛T₀F`
  have hK := concreteBase_isFlatColumnKflat hnear R0 hLj hFApin hχf hAN.flat hAN.free hR0
    hNSl.1 (hfl z hz)
  -- the column bound with a nonnegative constant
  have hb' : ∀ f, ‖(concreteBase D.Pl D.K (D.level n) (D.mu n z) hnear).DNinv
      ((concreteBase D.Pl D.K (D.level n) (D.mu n z) hnear).M
        ((concreteBase D.Pl D.K (D.level n) (D.mu n z) hnear).R f)) -
      (nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).flatColG (gRate D.Pl) (D.level n).ν_pos R0 f‖ ≤
      (|C₂| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₂ * Real.exp (-c' / retNu D.Pl D.σ₀ n)) * ‖f‖ := by
    intro f
    refine (hcol f).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hνi _)) (Real.exp_pos _).le)
      (norm_nonneg _)
  have hCb : 0 ≤ |C₂| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₂ * Real.exp (-c' / retNu D.Pl D.σ₀ n) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hνi _)) (Real.exp_pos _).le
  have hmain := curvedFlat_le _ _ R0 (D.level n).ν_pos hK hCb hb' hLnorm hFnorm
  rw [concreteReturnSeq_ops_eq D G n z hnear]
  refine hmain.trans ?_
  -- the exponents
  have hc2 : 0 < 2 * ‖D.Pl.signedCoeff D.σ₀‖ := mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)
  have hXle : X ≤ (retNu D.Pl D.σ₀ n)⁻¹ ^ k₄ / (2 * ‖D.Pl.signedCoeff D.σ₀‖) := by
    rw [hXdef, retEps_cube_mul D.coeff_ne n]
    exact div_le_div_of_nonneg_right (seq_rpow_le_inv_pow hνp hν1 _) hc2.le
  have hFF : 0 ≤ CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF *
      (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)) :=
    mul_nonneg (mul_nonneg hCF0 (pow_nonneg hνi _)) hCe'
  have hexp : Real.exp (-(c' - 1.1 * D.K.as) / retNu D.Pl D.σ₀ n) =
      Real.exp (-c' / retNu D.Pl D.σ₀ n) * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |CL| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kL * X *
        (|C₂| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₂ * Real.exp (-c' / retNu D.Pl D.σ₀ n)) *
        (CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF * (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n)))
      ≤ |CL| * (retNu D.Pl D.σ₀ n)⁻¹ ^ kL *
          ((retNu D.Pl D.σ₀ n)⁻¹ ^ k₄ / (2 * ‖D.Pl.signedCoeff D.σ₀‖)) *
          (|C₂| * (retNu D.Pl D.σ₀ n)⁻¹ ^ k₂ * Real.exp (-c' / retNu D.Pl D.σ₀ n)) *
          (CF * (retNu D.Pl D.σ₀ n)⁻¹ ^ kF *
            (Ce * Real.exp (1.1 * D.K.as / retNu D.Pl D.σ₀ n))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXle
            (mul_nonneg (abs_nonneg _) (pow_nonneg hνi _))) hCb) hFF
    _ = |CL| / (2 * ‖D.Pl.signedCoeff D.σ₀‖) * |C₂| * CF * Ce *
          ((concreteReturnSeq D G).ν n)⁻¹ ^ (kL + k₄ + k₂ + kF) *
          Real.exp (-(c' - 1.1 * D.K.as) / (concreteReturnSeq D G).ν n) := by
        show _ = |CL| / (2 * ‖D.Pl.signedCoeff D.σ₀‖) * |C₂| * CF * Ce *
          (retNu D.Pl D.σ₀ n)⁻¹ ^ (kL + k₄ + k₂ + kF) *
          Real.exp (-(c' - 1.1 * D.K.as) / retNu D.Pl D.σ₀ n)
        rw [hexp, pow_add, pow_add, pow_add]
        ring

end UnforcedLeray.Short.PartIIIb.NearInst
