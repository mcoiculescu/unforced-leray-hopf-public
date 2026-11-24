import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_9

/-!
# Decomposition of `LatCellHp` / `LatCellPsi` (tasks `PartIII-b:C/asrc/ra/9/1/2/9/1`, `/2`)

Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079.
Each word on `hpM` / `psiM` is termwise a bounded `(s∂_s)^i A^y` entry times a Gaussian polynomial
in `x_j`; this is the pointwise bound against the periodised Gaussian envelope `latEnv`.  The cell `L²`
norm of `latEnv` (against `Cyl.avgμ (cOf ν)`) is a single lemma shared by both.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Periodised Gaussian envelope `Σ_j (1+|x_j|)^m exp(-|x_j|²/(8(1+νs)))`, `x_j = x - j c e₁`,
`c = ν⁻²` (source 5063-5071). -/
def latEnv (m : ℕ) (ν s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' j : ℤ, (1 + ‖xj ν j x‖) ^ m * Real.exp (-(sq2 (xj ν j x)) / (8 * ageA ν s))

lemma latEnv_nonneg (m : ℕ) (ν s : ℝ) (x : ℝ × ℝ) : 0 ≤ latEnv m ν s x :=
  tsum_nonneg fun _ => by positivity

/-- Cell `L²` of the periodised Gaussian envelope (source 5076-5079): unfold against the lattice,
Cauchy-Schwarz with summable weights; `ν⁻ᵏ` absorbs `c = ν⁻²`. -/
def LatEnvCell : Prop :=
  ∀ m : ℕ, ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
      ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * latEnv m ν s x) ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k) ^ 2)

/-- Pointwise word bound on `hpM` (source 5063-5071): each word is a finite sum of
`(s∂_s)^i A^y` entries (`≤ M(A) s^{5/2}`) times Gaussian polynomials. -/
def HpWordPointwise (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (k m : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
    ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → ∀ w ∈ budgetWords, ∀ x : ℝ × ℝ,
        ‖wordW w (hpM ν χf A) (s, x)‖
          ≤ C * ν⁻¹ ^ k * affM ν χf A * s ^ (5 / 2 : ℝ) * latEnv m ν s x

/-- Pointwise word bound on `psiM` (same source lines). -/
def PsiWordPointwise (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (k m : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
    ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → ∀ w ∈ budgetWords, ∀ x : ℝ × ℝ,
        |wordW w (psiM ν χf A) (s, x)|
          ≤ C * ν⁻¹ ^ k * affM ν χf A * s ^ (5 / 2 : ℝ) * latEnv m ν s x

private lemma cell_combine (m : ℕ) (ν s : ℝ) (K D : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : ∀ x, |F x| ≤ K * latEnv m ν s x)
    (hD : ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * latEnv m ν s x) ^ 2)
        ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤ ENNReal.ofReal (D ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * |F x|) ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal ((K * D) ^ 2) := by
  have h1 : ∀ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * |F x|) ^ 2)
      ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (((1 + |x.2|) ^ 3 * latEnv m ν s x) ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (sq_nonneg K)]
    apply ENNReal.ofReal_le_ofReal
    have hG := latEnv_nonneg m ν s x
    have hb : |F x| ≤ |K| * latEnv m ν s x :=
      (hF x).trans (by gcongr; exact le_abs_self K)
    have h0 : 0 ≤ (1 + |x.2|) ^ 3 := by positivity
    have : (1 + |x.2|) ^ 3 * |F x| ≤ |K| * ((1 + |x.2|) ^ 3 * latEnv m ν s x) := by
      calc (1 + |x.2|) ^ 3 * |F x| ≤ (1 + |x.2|) ^ 3 * (|K| * latEnv m ν s x) := by gcongr
        _ = _ := by ring
    calc ((1 + |x.2|) ^ 3 * |F x|) ^ 2 ≤ (|K| * ((1 + |x.2|) ^ 3 * latEnv m ν s x)) ^ 2 := by
          gcongr
      _ = K ^ 2 * ((1 + |x.2|) ^ 3 * latEnv m ν s x) ^ 2 := by rw [mul_pow, sq_abs]
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (K ^ 2) *
        ENNReal.ofReal (((1 + |x.2|) ^ 3 * latEnv m ν s x) ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
        lintegral_mono h1
    _ = ENNReal.ofReal (K ^ 2) * ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * latEnv m ν s x) ^ 2)
        ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (D ^ 2) := by gcongr
    _ = ENNReal.ofReal ((K * D) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg K), mul_pow]

/-- `LatCellHp` from the pointwise word bound and the envelope cell bound. -/
theorem latCellHp_of (as : ℝ) (χf : ℝ → ℝ) (h1 : HpWordPointwise as χf) (h2 : LatEnvCell) :
    LatCellHp as χf := by
  intro hχ
  obtain ⟨C1, k1, m, n1, hC1, hn1, H1⟩ := h1 hχ
  obtain ⟨C2, k2, n2, hC2, hn2, H2⟩ := h2 m
  refine ⟨C1 * C2, k1 + k2, min n1 n2, mul_nonneg hC1 hC2, lt_min hn1 hn2, ?_⟩
  intro ν hν hνn A hA s hs hs1 w hw
  have := cell_combine m ν s (C1 * ν⁻¹ ^ k1 * affM ν χf A * s ^ (5 / 2 : ℝ)) (C2 * ν⁻¹ ^ k2)
    (fun x => ‖wordW w (hpM ν χf A) (s, x)‖) ?_
    (H2 ν hν (hνn.trans (min_le_right _ _)) s hs hs1)
  · convert this using 3
    · simp
    · rw [pow_add]; ring
  · intro x
    simpa using H1 ν hν (hνn.trans (min_le_left _ _)) A hA s hs hs1 w hw x

/-- `LatCellPsi` from the pointwise word bound and the envelope cell bound. -/
theorem latCellPsi_of (as : ℝ) (χf : ℝ → ℝ) (h1 : PsiWordPointwise as χf) (h2 : LatEnvCell) :
    LatCellPsi as χf := by
  intro hχ
  obtain ⟨C1, k1, m, n1, hC1, hn1, H1⟩ := h1 hχ
  obtain ⟨C2, k2, n2, hC2, hn2, H2⟩ := h2 m
  refine ⟨C1 * C2, k1 + k2, min n1 n2, mul_nonneg hC1 hC2, lt_min hn1 hn2, ?_⟩
  intro ν hν hνn A hA s hs hs1 w hw
  have := cell_combine m ν s (C1 * ν⁻¹ ^ k1 * affM ν χf A * s ^ (5 / 2 : ℝ)) (C2 * ν⁻¹ ^ k2)
    (fun x => wordW w (psiM ν χf A) (s, x)) ?_
    (H2 ν hν (hνn.trans (min_le_right _ _)) s hs hs1)
  · convert this using 3
    rw [pow_add]; ring
  · intro x
    exact H1 ν hν (hνn.trans (min_le_left _ _)) A hA s hs hs1 w hw x

end UnforcedLeray.Short.PartIIIb.Concrete
