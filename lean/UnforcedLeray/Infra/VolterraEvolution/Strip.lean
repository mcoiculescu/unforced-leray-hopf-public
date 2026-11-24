import UnforcedLeray.Infra.VolterraEvolution.Operator
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Volterra construction of the evolution family on a unit strip

For `VolterraData D` and `s ≤ τ ≤ s + 1` this file constructs the operators
`D.stripEvolution τ s : X →L[𝕜] X` solving

`E(τ,s) x = S₀(τ - s) x + ∫ r in s..τ, S (τ - r) (B r (E(r,s) x))`

(`paper/main.tex`, lines 292-306).  The construction is Picard iteration
`u₀ = S₀(· - s) x`, `u_{n+1} = vol s u_n`.  Convergence and uniqueness use the weighted
norm `sup e^{-λ(τ-s)} ‖u τ‖`: with `λ = 4 (C₀ β Γ(1/2))² + 1` the Volterra operator has
weighted norm at most `q = C₀ β Γ(1/2) λ^{-1/2} ≤ 1/2` (`norm_vol_le`), so the `n`-th
Picard term is bounded by `M₀ ‖x‖ qⁿ e^{λ(τ-s)}`.  This replaces the iterated
Beta-function bound `(C Γ(1/2))ⁿ (τ-s)^{n/2} / Γ(n/2+1)` by a geometric one.

Main results:
* `stripEvolution_eq` — the Volterra equation on the strip;
* `norm_stripEvolution_le` — the uniform bound `‖E(τ,s)‖ ≤ 2 M₀ e^λ`;
* `continuousOn_stripEvolution` — strong continuity in `τ` on `[s, s+1]`;
* `eqOn_stripEvolution`, `eq_stripEvolution_of_volterra` — uniqueness;
* `stripEvolution_comp` — the evolution law `E(τ,r) E(r,s) = E(τ,s)`;
* `stripEvolution_periodic` — periodicity for periodic coefficients.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

namespace VolterraData

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (D : VolterraData 𝕜 X Y)

/-! ### The weight and the contraction factor -/

/-- The exponential weight `λ = 4 (C₀ β Γ(1/2))² + 1`. -/
def lam : ℝ := 4 * (D.C₀ * D.β * Gamma (1 / 2)) ^ 2 + 1

/-- The weighted contraction factor `q = C₀ β λ^{-1/2} Γ(1/2)`. -/
def q : ℝ := D.C₀ * D.β * ((1 / D.lam) ^ (1 / 2 : ℝ) * Gamma (1 / 2))

/-- The uniform bound `2 M₀ e^λ` of the strip evolution. -/
def stripBound : ℝ := 2 * D.M₀ * exp D.lam

theorem lam_pos : 0 < D.lam := by unfold lam; positivity

theorem q_nonneg : 0 ≤ D.q := by
  unfold q
  have := D.C₀_nonneg; have := D.β_nonneg
  have : 0 ≤ Gamma (1 / 2 : ℝ) := Gamma_nonneg_of_nonneg (by norm_num)
  have : 0 ≤ (1 / D.lam) ^ (1 / 2 : ℝ) := rpow_nonneg (by have := D.lam_pos; positivity) _
  positivity

theorem q_le_half : D.q ≤ 1 / 2 := by
  set G := D.C₀ * D.β * Gamma (1 / 2) with hG
  have hG0 : 0 ≤ G := by
    have := D.C₀_nonneg; have := D.β_nonneg
    have : 0 ≤ Gamma (1 / 2 : ℝ) := Gamma_nonneg_of_nonneg (by norm_num)
    positivity
  have hlam : D.lam = 4 * G ^ 2 + 1 := rfl
  have hsq : 0 < √D.lam := Real.sqrt_pos.mpr D.lam_pos
  have h2G : 2 * G ≤ √D.lam := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * G)]
    exact Real.sqrt_le_sqrt (by rw [hlam]; nlinarith)
  have hq : D.q = G / √D.lam := by
    unfold q
    rw [show (1 / 2 : ℝ) = 1 / (2 : ℝ) from rfl, ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv,
      hG]
    ring
  rw [hq, div_le_iff₀ hsq]
  linarith

theorem q_lt_one : D.q < 1 := lt_of_le_of_lt D.q_le_half (by norm_num)

theorem stripBound_nonneg : 0 ≤ D.stripBound := by
  unfold stripBound; have := D.M₀_nonneg; positivity

/-- The geometric majorant of the Picard terms on the strip. -/
def major (x : X) (n : ℕ) : ℝ := D.M₀ * ‖x‖ * exp D.lam * D.q ^ n

theorem summable_major (x : X) : Summable (D.major x) :=
  (summable_geometric_of_lt_one D.q_nonneg D.q_lt_one).mul_left _

theorem hasSum_major (x : X) : HasSum (D.major x) (D.M₀ * ‖x‖ * exp D.lam * (1 - D.q)⁻¹) :=
  (hasSum_geometric_of_lt_one D.q_nonneg D.q_lt_one).mul_left _

variable [NormedSpace ℝ X]

/-! ### Picard iteration -/

/-- The Picard iterates `u₀ τ = S₀(τ - s) x`, `u_{n+1} = vol s u_n`. -/
def picard (s : ℝ) (x : X) : ℕ → ℝ → X
  | 0 => fun τ => D.S₀ (τ - s) x
  | n + 1 => D.vol s (picard s x n)

theorem picard_zero (s : ℝ) (x : X) (τ : ℝ) : D.picard s x 0 τ = D.S₀ (τ - s) x := rfl

theorem picard_succ (s : ℝ) (x : X) (n : ℕ) : D.picard s x (n + 1) = D.vol s (D.picard s x n) :=
  rfl

theorem continuousOn_picard (s : ℝ) (x : X) (n : ℕ) :
    ContinuousOn (D.picard s x n) (Icc s (s + 1)) := by
  induction n with
  | zero =>
    refine (D.continuousOn_S₀ x).comp (continuousOn_id.sub continuousOn_const) ?_
    intro τ hτ
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  | succ n ih =>
    rw [picard_succ]
    exact D.continuousOn_vol (by linarith) le_rfl ih

theorem norm_picard_le (s : ℝ) (x : X) (n : ℕ) :
    ∀ τ ∈ Icc s (s + 1), ‖D.picard s x n τ‖ ≤ D.M₀ * ‖x‖ * D.q ^ n * exp (D.lam * (τ - s)) := by
  induction n with
  | zero =>
    intro τ hτ
    rw [picard_zero, pow_zero, mul_one]
    have h1 : 1 ≤ exp (D.lam * (τ - s)) :=
      one_le_exp (mul_nonneg D.lam_pos.le (by linarith [hτ.1]))
    calc ‖D.S₀ (τ - s) x‖ ≤ ‖D.S₀ (τ - s)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ D.M₀ * ‖x‖ :=
          mul_le_mul_of_nonneg_right (D.norm_S₀_le _ (by linarith [hτ.1]) (by linarith [hτ.2]))
            (norm_nonneg _)
      _ ≤ D.M₀ * ‖x‖ * exp (D.lam * (τ - s)) :=
          le_mul_of_one_le_right (mul_nonneg D.M₀_nonneg (norm_nonneg _)) h1
  | succ n ih =>
    intro τ hτ
    rw [picard_succ]
    refine (D.norm_vol_le D.lam_pos hτ.1 hτ.2 (A := D.M₀ * ‖x‖ * D.q ^ n)
      (fun r hr => ih r ⟨hr.1, hr.2.trans hτ.2⟩)).trans (le_of_eq ?_)
    unfold q
    ring

theorem norm_picard_le_major {s : ℝ} (x : X) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) :
    ‖D.picard s x n τ‖ ≤ D.major x n := by
  refine (D.norm_picard_le s x n τ hτ).trans ?_
  unfold major
  have h1 : exp (D.lam * (τ - s)) ≤ exp D.lam :=
    exp_le_exp.mpr (by nlinarith [D.lam_pos, hτ.1, hτ.2])
  have h0 : 0 ≤ D.M₀ * ‖x‖ * D.q ^ n :=
    mul_nonneg (mul_nonneg D.M₀_nonneg (norm_nonneg _)) (pow_nonneg D.q_nonneg _)
  calc D.M₀ * ‖x‖ * D.q ^ n * exp (D.lam * (τ - s)) ≤ D.M₀ * ‖x‖ * D.q ^ n * exp D.lam :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = D.M₀ * ‖x‖ * exp D.lam * D.q ^ n := by ring

theorem picard_add (s : ℝ) (x y : X) (n : ℕ) :
    ∀ τ ∈ Icc s (s + 1), D.picard s (x + y) n τ = D.picard s x n τ + D.picard s y n τ := by
  induction n with
  | zero => intro τ _; simp [picard_zero]
  | succ n ih =>
    intro τ hτ
    rw [picard_succ, picard_succ, picard_succ,
      D.vol_congr hτ.1 (g := fun r => D.picard s x n r + D.picard s y n r)
        (fun r hr => ih r ⟨hr.1, hr.2.trans hτ.2⟩)]
    exact D.vol_add hτ.1 hτ.2 ((D.continuousOn_picard s x n).mono (Icc_subset_Icc_right hτ.2))
      ((D.continuousOn_picard s y n).mono (Icc_subset_Icc_right hτ.2))

theorem picard_smul [SMulCommClass ℝ 𝕜 X] (s : ℝ) (c : 𝕜) (x : X) (n : ℕ) :
    ∀ τ ∈ Icc s (s + 1), D.picard s (c • x) n τ = c • D.picard s x n τ := by
  induction n with
  | zero => intro τ _; simp [picard_zero]
  | succ n ih =>
    intro τ hτ
    rw [picard_succ, picard_succ,
      D.vol_congr hτ.1 (g := fun r => c • D.picard s x n r)
        (fun r hr => ih r ⟨hr.1, hr.2.trans hτ.2⟩)]
    exact D.vol_smul s τ c _

/-! ### The solution -/

/-- The sum of the Picard series. -/
def sol (s : ℝ) (x : X) (τ : ℝ) : X := ∑' n, D.picard s x n τ

variable [CompleteSpace X]

theorem summable_picard {s : ℝ} (x : X) {τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) :
    Summable (fun n => D.picard s x n τ) :=
  Summable.of_norm_bounded (D.summable_major x) (fun n => D.norm_picard_le_major x n hτ)

omit [CompleteSpace X] in
theorem norm_sol_le {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) (x : X) :
    ‖D.sol s x τ‖ ≤ D.stripBound * ‖x‖ := by
  refine (tsum_of_norm_bounded (D.hasSum_major x) (fun n => D.norm_picard_le_major x n hτ)).trans ?_
  have h1q : 1 / 2 ≤ 1 - D.q := by linarith [D.q_le_half]
  have hinv : (1 - D.q)⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) h1q
    simpa [one_div] using h
  have h0 : 0 ≤ D.M₀ * ‖x‖ * exp D.lam := by
    have := D.M₀_nonneg; positivity
  calc D.M₀ * ‖x‖ * exp D.lam * (1 - D.q)⁻¹ ≤ D.M₀ * ‖x‖ * exp D.lam * 2 :=
        mul_le_mul_of_nonneg_left hinv h0
    _ = D.stripBound * ‖x‖ := by unfold stripBound; ring

theorem continuousOn_sol (s : ℝ) (x : X) : ContinuousOn (D.sol s x) (Icc s (s + 1)) :=
  continuousOn_tsum (D.continuousOn_picard s x) (D.summable_major x)
    (fun n _ hτ => D.norm_picard_le_major x n hτ)

theorem sol_add {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) (x y : X) :
    D.sol s (x + y) τ = D.sol s x τ + D.sol s y τ := by
  unfold sol
  rw [tsum_congr (fun n => D.picard_add s x y n τ hτ)]
  exact ((D.summable_picard x hτ).hasSum.add (D.summable_picard y hτ).hasSum).tsum_eq

theorem sol_smul [SMulCommClass ℝ 𝕜 X] {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) (c : 𝕜) (x : X) :
    D.sol s (c • x) τ = c • D.sol s x τ := by
  unfold sol
  rw [tsum_congr (fun n => D.picard_smul s c x n τ hτ)]
  exact ((D.summable_picard x hτ).hasSum.const_smul c).tsum_eq

/-- The Picard sum solves the Volterra equation on the strip. -/
theorem sol_eq {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) (x : X) :
    D.sol s x τ = D.S₀ (τ - s) x + D.vol s (D.sol s x) τ := by
  unfold sol
  rw [(D.summable_picard x hτ).tsum_eq_zero_add, picard_zero]
  congr 1
  simp only [picard_succ]
  refine (?_ : HasSum (fun n => D.vol s (D.picard s x n) τ) (D.vol s (fun r => ∑' n,
    D.picard s x n r) τ)).tsum_eq
  unfold vol
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n r => D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * D.major x n) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (D.intervalIntegrable_integrand hτ.1 hτ.2
      ((D.continuousOn_picard s x n).mono (Icc_subset_Icc_right hτ.2))).def'.aestronglyMeasurable
  · intro n
    filter_upwards [ae_ne_real τ] with r hrτ hr
    rw [uIoc_of_le hτ.1] at hr
    have hr' : r ∈ Ico s τ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrτ⟩
    refine (D.norm_integrand_le hτ.2 hr' _).trans ?_
    refine mul_le_mul_of_nonneg_left
      (D.norm_picard_le_major x n ⟨hr'.1, hr'.2.le.trans hτ.2⟩) ?_
    exact mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg) (rpow_nonneg (by linarith [hr'.2]) _)
  · exact Eventually.of_forall fun r _ => (D.summable_major x).mul_left _
  · simp_rw [tsum_mul_left]
    exact ((intervalIntegrable_kernel τ s τ).const_mul (D.C₀ * D.β)).mul_const _
  · refine Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le hτ.1] at hr
    have h := (D.summable_picard x (s := s) (τ := r) ⟨hr.1.le, hr.2.trans hτ.2⟩).hasSum
    exact (D.S (τ - r)).hasSum ((D.B r).hasSum h)

/-! ### The strip evolution operators -/

/-- The strip evolution `E(τ,s) : X →L[𝕜] X` for `s ≤ τ ≤ s + 1` (and `0` off the strip). -/
def stripEvolution [SMulCommClass ℝ 𝕜 X] (τ s : ℝ) : X →L[𝕜] X :=
  if h : τ ∈ Icc s (s + 1) then
    LinearMap.mkContinuous
      { toFun := fun x => D.sol s x τ
        map_add' := fun x y => D.sol_add h x y
        map_smul' := fun c x => by rw [RingHom.id_apply]; exact D.sol_smul h c x }
      D.stripBound (fun x => D.norm_sol_le h x)
  else 0

variable [SMulCommClass ℝ 𝕜 X]

theorem stripEvolution_apply {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) (x : X) :
    D.stripEvolution τ s x = D.sol s x τ := by
  rw [stripEvolution, dif_pos hτ]
  rfl

theorem stripEvolution_of_notMem {s τ : ℝ} (hτ : τ ∉ Icc s (s + 1)) :
    D.stripEvolution τ s = 0 := by
  rw [stripEvolution, dif_neg hτ]

/-- **Volterra equation.** On the strip `s ≤ τ ≤ s + 1`,
`E(τ,s) x = S₀(τ - s) x + ∫ r in s..τ, S (τ - r) (B r (E(r,s) x))`. -/
theorem stripEvolution_eq {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) (x : X) :
    D.stripEvolution τ s x =
      D.S₀ (τ - s) x + ∫ r in s..τ, D.S (τ - r) (D.B r (D.stripEvolution r s x)) := by
  rw [D.stripEvolution_apply hτ, D.sol_eq hτ]
  congr 1
  exact D.vol_congr hτ.1 (fun r hr => (D.stripEvolution_apply ⟨hr.1, hr.2.trans hτ.2⟩ x).symm)

/-- **Uniform bound** on the strip: `‖E(τ,s)‖ ≤ 2 M₀ e^λ` (in fact for all `τ, s`). -/
theorem norm_stripEvolution_le (τ s : ℝ) : ‖D.stripEvolution τ s‖ ≤ D.stripBound := by
  by_cases hτ : τ ∈ Icc s (s + 1)
  · rw [stripEvolution, dif_pos hτ]
    exact LinearMap.mkContinuous_norm_le _ D.stripBound_nonneg _
  · rw [D.stripEvolution_of_notMem hτ, norm_zero]
    exact D.stripBound_nonneg

/-- **Strong continuity** in `τ` on `[s, s + 1]`. -/
theorem continuousOn_stripEvolution (s : ℝ) (x : X) :
    ContinuousOn (fun τ => D.stripEvolution τ s x) (Icc s (s + 1)) :=
  (D.continuousOn_sol s x).congr fun _ hτ => D.stripEvolution_apply hτ x

theorem stripEvolution_self (s : ℝ) : D.stripEvolution s s = D.S₀ 0 := by
  ext x
  rw [D.stripEvolution_eq ⟨le_rfl, by linarith⟩ x, sub_self, intervalIntegral.integral_same,
    add_zero]

/-! ### Uniqueness -/

omit [CompleteSpace X] [SMulCommClass ℝ 𝕜 X] in
/-- A continuous solution of the homogeneous Volterra equation on `[s, T]`, `T ≤ s + 1`,
vanishes identically there. -/
theorem eq_zero_of_homogeneous {s T : ℝ} (hT : T ≤ s + 1) {w : ℝ → X}
    (hw : ContinuousOn w (Icc s T)) (heq : ∀ τ ∈ Icc s T, w τ = D.vol s w τ) :
    ∀ τ ∈ Icc s T, w τ = 0 := by
  obtain ⟨A₀, hA₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  set A := max A₀ 0
  have hA0 : 0 ≤ A := le_max_right _ _
  have hbd : ∀ n : ℕ, ∀ τ ∈ Icc s T, ‖w τ‖ ≤ A * D.q ^ n * exp (D.lam * (τ - s)) := by
    intro n
    induction n with
    | zero =>
      intro τ hτ
      rw [pow_zero, mul_one]
      exact ((hA₀ τ hτ).trans (le_max_left _ _)).trans
        (le_mul_of_one_le_right hA0 (one_le_exp (mul_nonneg D.lam_pos.le (by linarith [hτ.1]))))
    | succ n ih =>
      intro τ hτ
      rw [heq τ hτ]
      refine (D.norm_vol_le D.lam_pos hτ.1 (hτ.2.trans hT) (A := A * D.q ^ n)
        (fun r hr => ih r ⟨hr.1, hr.2.trans hτ.2⟩)).trans (le_of_eq ?_)
      unfold q
      ring
  intro τ hτ
  have hlim : Tendsto (fun n : ℕ => A * D.q ^ n * exp (D.lam * (τ - s))) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one D.q_nonneg D.q_lt_one).const_mul A).mul_const
      (exp (D.lam * (τ - s)))
    simpa using this
  have h0 : ‖w τ‖ ≤ 0 := ge_of_tendsto' hlim (fun n => hbd n τ hτ)
  exact norm_le_zero_iff.mp h0

/-- **Uniqueness.** A function continuous on `[s, T]` (`T ≤ s + 1`) solving the Volterra
equation with datum `x` there coincides with `E(·,s) x` on `[s, T]`. -/
theorem eqOn_stripEvolution {s T : ℝ} (hT : T ≤ s + 1) {x : X} {u : ℝ → X}
    (hu : ContinuousOn u (Icc s T))
    (heq : ∀ τ ∈ Icc s T, u τ = D.S₀ (τ - s) x + ∫ r in s..τ, D.S (τ - r) (D.B r (u r))) :
    ∀ τ ∈ Icc s T, u τ = D.stripEvolution τ s x := by
  have hsub : Icc s T ⊆ Icc s (s + 1) := Icc_subset_Icc_right hT
  have hv : ContinuousOn (D.sol s x) (Icc s T) := (D.continuousOn_sol s x).mono hsub
  have hw : ContinuousOn (fun τ => u τ - D.sol s x τ) (Icc s T) := hu.sub hv
  have hzero := D.eq_zero_of_homogeneous hT hw (fun τ hτ => by
    have hτ' : τ ∈ Icc s (s + 1) := hsub hτ
    rw [D.vol_sub hτ.1 hτ'.2 (hu.mono (Icc_subset_Icc_right hτ.2))
      (hv.mono (Icc_subset_Icc_right hτ.2)), heq τ hτ, D.sol_eq hτ' x]
    simp only [vol]
    abel)
  intro τ hτ
  rw [D.stripEvolution_apply (hsub hτ)]
  exact sub_eq_zero.mp (hzero τ hτ)

/-- **Uniqueness of the family.** Any family of operators that is strongly continuous on the
strip and satisfies the Volterra equation there equals `stripEvolution` on the strip. -/
theorem eq_stripEvolution_of_volterra (s : ℝ) (E' : ℝ → X →L[𝕜] X)
    (hcont : ∀ x, ContinuousOn (fun τ => E' τ x) (Icc s (s + 1)))
    (heq : ∀ τ ∈ Icc s (s + 1), ∀ x,
      E' τ x = D.S₀ (τ - s) x + ∫ r in s..τ, D.S (τ - r) (D.B r (E' r x))) :
    ∀ τ ∈ Icc s (s + 1), E' τ = D.stripEvolution τ s := by
  intro τ hτ
  ext x
  exact D.eqOn_stripEvolution le_rfl (hcont x) (fun τ' hτ' => heq τ' hτ' x) τ hτ

end VolterraData

end UnforcedLeray.Infra.VolterraEvolution
