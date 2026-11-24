import UnforcedLeray.Short.PartI.Sub.T04.APriori
import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Sub.T08Statement

/-!
# Part I, task `PartI:T04/8` (`APElliptic`): decomposition

Source: `the November 2 reference manuscript` lines 285-287 (vorticity energy
identities and their elliptic step).  For a divergence-free smooth periodic `f` and `j`,
`∫‖D^{j+1} f‖² ≤ 2^{2j+2} ∫‖D^j curl f‖²`.  The proof is split into

* `APEllipticA`: the cell identity `∫ Σ_{|w|=j} Σ_k |∇ ∂_w f_k|² = ∫ Σ_{|w|=j} (∂_w curl f)²`
  (integration by parts in `q` periodic, in `η` with cutoffs and `R → ∞`);
* `APEllipticB`, `APEllipticC`: the pointwise comparisons of operator norms with coordinate words;
* `APEllipticD`: integrability of `‖D^j curl f‖²`;

and `apElliptic_of` assembles them with constant `K = 2^(2j+2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The hypotheses of `APElliptic` on a field `f` (lines 285-287): `c ≥ 1`, `f` smooth, `c`-periodic,
divergence free, all derivatives bounded and square integrable on the cell. -/
def APEllipticData (c : ℝ) (f : Plane → Vec) : Prop :=
  1 ≤ c ∧ ContDiff ℝ ∞ f ∧ Cyl.IsPeriodic c f ∧ (∀ z, Cyl.divergence f z = 0) ∧
    (∀ i : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ M) ∧
    (∀ i : ℕ, IntegrableOn (fun z => ‖iteratedFDeriv ℝ i f z‖ ^ 2) (Cyl.cell c))

/-- Gradient energy of the order-`j` coordinate words of `f`, pointwise. -/
def wordGradSq (j : ℕ) (f : Plane → Vec) (z : Plane) : ℝ :=
  ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
    (Cyl.partialQ (wordComp w f k) z ^ 2 + Cyl.partialEta (wordComp w f k) z ^ 2)

/-- Squared order-`j` coordinate words of the scalar curl of `f`, pointwise. -/
def wordCurlSq (j : ℕ) (f : Plane → Vec) (z : Plane) : ℝ :=
  ∑ w ∈ wordsOfLength j, B0151.derivWord w (Cyl.curl f) z ^ 2

/-- **Cell identity** (lines 285-287, "transverse cutoffs"): for `f` as in `APEllipticData` and every
`j`, `∫_cell Σ_{|w|=j} Σ_k |∇ ∂_w f_k|² = ∫_cell Σ_{|w|=j} (∂_w curl f)²`, both integrands being
integrable.  Route: for each word `g = ∂_w f` is smooth, periodic, divergence free (derivatives
commute), with bounded `L²` derivatives, and `|∂_q g|² + |∂_η g|² - (curl g)² - (div g)² =
2(∂_q g_η ∂_η g_q - ∂_q g_q ∂_η g_η)`; the integral of `∂_q g_η ∂_η g_q - ∂_q g_q ∂_η g_η` vanishes
(`Sob.integral_cylCell_fderiv_eq_zero` in `q`; in `η` with `etaCutoff R`, `R → ∞`, as in
`GradL2OfLapL2`); `∂_w` commutes with `curl`. -/
def APEllipticA : Prop :=
  ∀ (j : ℕ) (c : ℝ) (f : Plane → Vec), APEllipticData c f →
    IntegrableOn (wordGradSq j f) (Cyl.cell c) ∧ IntegrableOn (wordCurlSq j f) (Cyl.cell c) ∧
      ∫ z in Cyl.cell c, wordGradSq j f z = ∫ z in Cyl.cell c, wordCurlSq j f z

/-- **Pointwise jet bound** (`cylJetWord_proof` componentwise): `‖D^{j+1} f z‖² ≤ 2^{j+2}` times the
gradient energy of the order-`j` words.  Route: `‖x‖ ≤ |x 0| + |x 1|`, `‖D^l f z‖ ≤ Σ_k ‖D^l f_k z‖
≤ Σ_k Σ_{|w'|=l} |∂_{w'} f_k z|`, Cauchy-Schwarz over `2·2^{j+1}` terms, and
`wordsOfLength (j+1)` consists of `true :: w`, `false :: w` (`derivWord (b :: w) = partial_b (derivWord w)`). -/
def APEllipticB : Prop :=
  ∀ (j : ℕ) (c : ℝ) (f : Plane → Vec), APEllipticData c f → ∀ z : Plane,
    ‖iteratedFDeriv ℝ (j + 1) f z‖ ^ 2 ≤ 2 ^ (j + 2) * wordGradSq j f z

/-- **Pointwise word bound** for the curl: `Σ_{|w|=j} (∂_w curl f z)² ≤ 2^j ‖D^j curl f z‖²`
(`cylJetWord_proof`, first part, applied to the smooth function `curl f`; `|wordsOfLength j| ≤ 2^j`). -/
def APEllipticC : Prop :=
  ∀ (j : ℕ) (c : ℝ) (f : Plane → Vec), APEllipticData c f → ∀ z : Plane,
    wordCurlSq j f z ≤ 2 ^ j * ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2

/-- **Integrability of the curl jets**: `‖D^j curl f‖² ∈ L¹(cell)`.  Route: `curl f` is a fixed
linear image of `Df`, so `‖D^j curl f z‖ ≤ 2‖D^{j+1} f z‖`, and `‖D^{j+1} f‖²` is integrable. -/
def APEllipticD : Prop :=
  ∀ (j : ℕ) (c : ℝ) (f : Plane → Vec), APEllipticData c f →
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2) (Cyl.cell c)

theorem apElliptic_of (hA : APEllipticA) (hB : APEllipticB) (hC : APEllipticC)
    (hD : APEllipticD) : APElliptic := by
  intro j
  refine ⟨2 ^ (2 * j + 2), by positivity, ?_⟩
  intro c hc f hf hp hd hb hi
  have hdata : APEllipticData c f := ⟨hc, hf, hp, hd, hb, hi⟩
  obtain ⟨hL, hR, hEq⟩ := hA j c f hdata
  have hDj := hD j c f hdata
  have hms : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have h1 : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) f z‖ ^ 2 ≤
      ∫ z in Cyl.cell c, 2 ^ (j + 2) * wordGradSq j f z :=
    setIntegral_mono_on (hi (j + 1)) (hL.const_mul _) hms (fun z _ => hB j c f hdata z)
  have h2 : ∫ z in Cyl.cell c, wordCurlSq j f z ≤
      ∫ z in Cyl.cell c, 2 ^ j * ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2 :=
    setIntegral_mono_on hR (hDj.const_mul _) hms (fun z _ => hC j c f hdata z)
  rw [integral_const_mul] at h1 h2
  rw [hEq] at h1
  have h3 : (2 : ℝ) ^ (j + 2) * (2 ^ j * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2)
      = 2 ^ (2 * j + 2) * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2 := by
    rw [← mul_assoc, ← pow_add]; congr 2; ring
  calc _ ≤ _ := h1
    _ ≤ (2 : ℝ) ^ (j + 2) * (2 ^ j * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := h3

end UnforcedLeray.Short.PartI
