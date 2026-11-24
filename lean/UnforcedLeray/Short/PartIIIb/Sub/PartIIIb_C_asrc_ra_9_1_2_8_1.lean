import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_1.Helpers

/-!
# `PartIII-b:C/asrc/ra/9/1/2/8/1` : `geoDcThetaBound` reduced to scalar chart-calculus lemmas

Source of record: `the November 2 reference manuscript`,
lines 5034-5039, 4979-4980.  `Θ = (0, φ)`, `φ = ψ - 𝒦ψ`, `𝒦 = η∂_η + 2s∂_s`.  With the conormal words
`D0 = s∂_s`, `D1 = ∂_q`, `D2 = ∂_η` (`wordW`), the scalar `Dc φ = ∂_sφ + (μ/s)φ - ν(∂_q²+∂_η²)φ`
is an explicit combination of the words `[], [0],[2],[0,0],[0,2],[1,1],[2,2],[1,1,0],[1,1,2],[2,2,0],[2,2,2]`
(all of length `≤ 3`), written with no commutation of derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Scalar `Dc`: `(∂_s + μ/s - ν(∂_q²+∂_η²)) φ`. -/
def DcR (ν μ : ℝ) (φ : Chart → ℝ) : Chart → ℝ := fun p =>
  UnforcedLeray.Axi.dS φ p + (μ / p.1) * φ p
    - ν * (UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ φ) p
      + UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta φ) p)

/-- `φ = (1-𝒦)ψ`. -/
def thetaScal (ψ : Chart → ℝ) : Chart → ℝ := fun p => ψ p - Kc ψ p

/-- `Dc` only depends on the germ at `q` (it uses derivatives up to order two). -/
def DcLocalP : Prop :=
  ∀ (ν μ : ℝ) (F G : Chart → Merid) (q : Chart), F =ᶠ[nhds q] G → Dc ν μ F q = Dc ν μ G q

/-- `Dc` of `(0, φ)` is `(0, Dc φ)` for `φ` of class `C²` at `q` (`toMer (0,·)` is a continuous
linear embedding). -/
def DcToMerP : Prop :=
  ∀ (ν μ : ℝ) (φ : Chart → ℝ) (q : Chart), ContDiffAt ℝ 2 φ q →
    Dc ν μ (fun p => toMer (0, φ p)) q = toMer (0, DcR ν μ φ q)

/-- `(1-𝒦)ψ` is `C²` at `q` when `ψ` is `C⁴` on the open set `s > 0`. -/
def ThetaScalSmoothP : Prop :=
  ∀ (ψ : Chart → ℝ) (q : Chart), 0 < q.1 → ContDiffOn ℝ 4 ψ (Ioi 0 ×ˢ univ) →
    ContDiffAt ℝ 2 (thetaScal ψ) q

/-- `s ∂_s φ = [] - η·[0,2] - 2·[0,0]` words: `s·dS (thetaScal ψ) = w0 - η w02 - 2 w00`
(`D0` commutes with multiplication by `η`; `D0 (s ∂_s ψ) = wordW [0,0] ψ`). -/
def ThetaScalDSP : Prop :=
  ∀ (ψ : Chart → ℝ) (q : Chart), 0 < q.1 → ContDiffOn ℝ 4 ψ (Ioi 0 ×ˢ univ) →
    q.1 * UnforcedLeray.Axi.dS (thetaScal ψ) q
      = wordW [0] ψ q - q.2.2 * wordW [0, 2] ψ q - 2 * wordW [0, 0] ψ q

/-- `∂_q² φ = [1,1] - η·[1,1,2] - 2·[1,1,0]` (`∂_q` commutes with `η` and with `s`). -/
def ThetaScalDQQP : Prop :=
  ∀ (ψ : Chart → ℝ) (q : Chart), 0 < q.1 → ContDiffOn ℝ 4 ψ (Ioi 0 ×ˢ univ) →
    UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (thetaScal ψ)) q
      = wordW [1, 1] ψ q - q.2.2 * wordW [1, 1, 2] ψ q - 2 * wordW [1, 1, 0] ψ q

/-- `∂_η² φ = -[2,2] - η·[2,2,2] - 2·[2,2,0]` (`∂_η² (η f) = 2 ∂_η f + η ∂_η² f`). -/
def ThetaScalDEEP : Prop :=
  ∀ (ψ : Chart → ℝ) (q : Chart), 0 < q.1 → ContDiffOn ℝ 4 ψ (Ioi 0 ×ˢ univ) →
    UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (thetaScal ψ)) q
      = -wordW [2, 2] ψ q - q.2.2 * wordW [2, 2, 2] ψ q - 2 * wordW [2, 2, 0] ψ q

/-- The word bound: with `a = q.1`, `η = q.2.2` and `w_i` the real numbers
`wordW w ψ q`, the explicit combination has absolute value `≤ C (1+a⁻¹)(1+|η|)³ Σ_{w∈budgetWords}|w|`
(`|μ| ≤ 1`, `0<ν≤1`, each listed word has length `≤ 3` so lies in `budgetWords`, `Finset.single_le_sum`). -/
def ThetaScalBoundP : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Chart → ℝ) (q : Chart) (ν μ : ℝ), 0 < q.1 → 0 < ν → ν ≤ 1 → |μ| ≤ 1 →
    |q.1⁻¹ * (wordW [0] ψ q - q.2.2 * wordW [0, 2] ψ q - 2 * wordW [0, 0] ψ q)
      + μ / q.1 * (wordW [] ψ q - 2 * wordW [0] ψ q - q.2.2 * wordW [2] ψ q)
      - ν * ((wordW [1, 1] ψ q - q.2.2 * wordW [1, 1, 2] ψ q - 2 * wordW [1, 1, 0] ψ q)
        + (-wordW [2, 2] ψ q - q.2.2 * wordW [2, 2, 2] ψ q - 2 * wordW [2, 2, 0] ψ q))|
      ≤ C * (1 + q.1⁻¹) * (1 + |q.2.2|) ^ 3 * ∑ w ∈ budgetWords, |wordW w ψ q|

/-- `thetaM` is, near `q` (`s > 0`), the embedding `(0, (1-𝒦)ψ)` (by `kop_chart_eq`). -/
theorem thetaM_eventuallyEq (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (q : Chart) (hq : 0 < q.1)
    (hp : ContDiffOn ℝ 4 (psiM ν χf A) (Ioi 0 ×ˢ univ)) :
    thetaM ν χf A =ᶠ[nhds q] fun p => toMer (0, thetaScal (psiM ν χf A) p) := by
  have hU : IsOpen ((Ioi (0:ℝ)) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : q ∈ (Ioi (0:ℝ)) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hq, mem_univ _⟩
  filter_upwards [hU.mem_nhds hmem] with p hpU
  have hd : DifferentiableAt ℝ (psiM ν χf A) p :=
    ((hp.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num))
  have hk := kop_chart_eq (psiM ν χf A) p.1 p.2 hd
  simp only [thetaM, thetaScal, Kc]
  congr 2
  have : Kop (fun s' y => psipA ν χf A s' y) p.1 p.2 = Kop (fun s' y => psiM ν χf A (s', y)) p.1 p.2 := rfl
  rw [this, hk]
  simp only [smul_eq_mul, psiM]
  ring

/-- **Assembly**: `geoDcThetaBound` from the scalar lemmas. -/
theorem geoDcThetaBound_of (as : ℝ) (χf : ℝ → ℝ) (h1 : DcLocalP) (h2 : DcToMerP)
    (h3 : ThetaScalSmoothP) (h4 : ThetaScalDSP) (h5 : ThetaScalDQQP) (h6 : ThetaScalDEEP)
    (h7 : ThetaScalBoundP) : GeoDcThetaBound as χf := by
  obtain ⟨C, hC0, hC⟩ := h7
  refine ⟨C, hC0, fun _ ν μ ε hν hν1 hμ _ _ A _ _ hp q hq => ?_⟩
  set ψ := psiM ν χf A with hψ
  have e1 : Dc ν μ (thetaM ν χf A) q = toMer (0, DcR ν μ (thetaScal ψ) q) :=
    (h1 ν μ _ _ q (thetaM_eventuallyEq ν χf A q hq hp)).trans (h2 ν μ _ q (h3 ψ q hq hp))
  have e2 : DcR ν μ (thetaScal ψ) q
      = q.1⁻¹ * (wordW [0] ψ q - q.2.2 * wordW [0, 2] ψ q - 2 * wordW [0, 0] ψ q)
      + μ / q.1 * (wordW [] ψ q - 2 * wordW [0] ψ q - q.2.2 * wordW [2] ψ q)
      - ν * ((wordW [1, 1] ψ q - q.2.2 * wordW [1, 1, 2] ψ q - 2 * wordW [1, 1, 0] ψ q)
        + (-wordW [2, 2] ψ q - q.2.2 * wordW [2, 2, 2] ψ q - 2 * wordW [2, 2, 0] ψ q)) := by
    have a := h4 ψ q hq hp
    have b := h5 ψ q hq hp
    have c := h6 ψ q hq hp
    have hq' : q.1 ≠ 0 := hq.ne'
    have a' : UnforcedLeray.Axi.dS (thetaScal ψ) q = q.1⁻¹ * (q.1 * UnforcedLeray.Axi.dS (thetaScal ψ) q) := by
      field_simp
    unfold DcR
    rw [a', a, b, c]
    simp only [thetaScal, Kc, wordW, opW, smul_eq_mul]
    ring
  rw [e1, e2, norm_toMer_zero]
  have := hC ψ q ν μ hq hν hν1 hμ
  refine this.trans ?_
  have hnn : 0 ≤ C * (1 + q.1⁻¹) * (1 + |q.2.2|) ^ 3 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hnn
  exact Finset.sum_le_sum fun w _ => le_add_of_nonneg_left (norm_nonneg _)

end UnforcedLeray.Short.PartIIIb.Concrete
