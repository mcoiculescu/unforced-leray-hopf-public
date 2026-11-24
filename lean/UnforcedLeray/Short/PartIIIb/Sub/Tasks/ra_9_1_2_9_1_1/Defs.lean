import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_9_Env

/-!
# Decomposition of `hpWordPointwise` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1`)

Source `the November 2 reference manuscript`
lines 5063-5071, 5076-5079: each conormal word of length `≤ 4` on `h^p_A` is termwise (lattice sum
over `j`) a finite sum of `(s∂_s)^i A^y` entries times Gaussian polynomials in `x_j`.

Architecture: `hpM = Σ_j hpSummandM j` (`HpSumDecomp`); every summand is `C⁴` on `s > 0`
(`HpSummandSmooth`) and its words have the envelope bound `C · M(A) s^{5/2} · (1+|x_j|)^m
exp(-|x_j|²/(8a))` for all `s > 0` (`HpSummandBound`; for `νs ≥ 1.1` the summand and all its words
vanish since `A^y = 0` there); the envelope bound gives a locally uniform summable majorant
(`EnvLocSumm`); locally uniform summable majorants of all words allow termwise conormal
differentiation (`TermwiseWord`); the envelope is summable (`EnvSummable`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The open chart region `s > 0`. -/
def UChart : Set Chart := Ioi 0 ×ˢ univ

/-- The `j`-th lattice summand of `h^p_A` as a chart function (source 4981-4985):
`toMer([V_j, A^y_mer x_j])`. -/
def hpSummandM (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) : Chart → Merid :=
  fun p => toMer (merApply (Ay ν χf A p.1) (Vj ν p.1 j p.2)
    - fderiv ℝ (Vj ν p.1 j) p.2 (merApply (Ay ν χf A p.1) (xj ν j p.2)))

/-- The envelope term `(1+|x_j|)^m exp(-|x_j|²/(8a))` of `latEnv`. -/
def envTerm (m : ℕ) (ν : ℝ) (j : ℤ) (p : Chart) : ℝ :=
  (1 + ‖xj ν j p.2‖) ^ m * Real.exp (-(sq2 (xj ν j p.2)) / (8 * ageA ν p.1))

/-- Locally uniform summable majorant on `s > 0`. -/
def LocSumm (G : ℤ → Chart → Merid) : Prop :=
  ∀ p ∈ UChart, ∃ N ∈ 𝓝 p, ∃ u : ℤ → ℝ, Summable u ∧ ∀ j, ∀ q ∈ N, ‖G j q‖ ≤ u j

/-- `h^p_A` is the lattice sum of the summands (`toMer` is a linear equivalence, so it commutes
with `tsum` without a summability hypothesis). -/
def HpSumDecomp : Prop :=
  ∀ (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3),
    hpM ν χf A = fun p => ∑' j : ℤ, hpSummandM ν χf A j p

/-- Each summand is `C⁴` on `s > 0` (`A^y = χ_f A` is `C⁶` on `s > 0`, `V_j` is smooth; source
4741-4745 and 4991). -/
def HpSummandSmooth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ j : ℤ,
    ContDiffOn ℝ 4 (hpSummandM ν χf A j) UChart

/-- Word bound for one summand (source 5063-5071), for all `s > 0`: for `0 < νs ≤ 1.1`,
`(s∂_s)^i A^y` entries are `≤ M(A) s^{5/2}` (`le_csSup`, `BddAbove` from `IsAffElem.bdd` and the
smooth compactly supported cutoff) and `a ∈ [1, 2.1]`; for `νs ≥ 1.1` the summand vanishes
identically near `s` (as `A^y = 0` there), so all its words vanish. -/
def HpSummandBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
    ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s →
      ∀ w ∈ budgetWords, ∀ (x : ℝ × ℝ) (j : ℤ),
        ‖wordW w (hpSummandM ν χf A j) (s, x)‖
          ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x)

/-- The envelope is summable over the lattice. -/
def EnvSummable : Prop :=
  ∀ (m : ℕ) (ν : ℝ), 0 < ν → ∀ p : Chart, 0 < p.1 → Summable (fun j : ℤ => envTerm m ν j p)

/-- A pointwise envelope bound `‖G j p‖ ≤ K s^{5/2} envTerm` on `s > 0` yields a locally
uniform summable majorant (on a neighbourhood `|s'-s|<s/2`, `|x'-x|<1`: `a' ≤ 1+ν·3s/2`,
`|x'_j| ≥ |x_j|-1`, then `gp_poly_summable`/`gp_gauss_summable` in
`Concrete/ReturnInst/HpPsiTermSummable/Gauss.lean`). -/
def EnvLocSumm : Prop :=
  ∀ (m : ℕ) (ν K : ℝ), 0 < ν → ∀ G : ℤ → Chart → Merid,
    (∀ j, ∀ p ∈ UChart, ‖G j p‖ ≤ K * p.1 ^ (5 / 2 : ℝ) * envTerm m ν j p) → LocSumm G

/-- Termwise conormal differentiation of a lattice sum whose words of length `≤ 4` have locally
uniform summable majorants and whose summands are `C⁴` (induction on the word, using
`hasFDerivAt_tsum`/`HasFDerivAt` for series with locally uniformly summable derivatives, and
that `UChart` is open so equality on `UChart` passes to `fderiv`). -/
def TermwiseWord : Prop :=
  ∀ F : ℤ → Chart → Merid, (∀ j, ContDiffOn ℝ 4 (F j) UChart) →
    (∀ w ∈ budgetWords, LocSumm (fun j => wordW w (F j))) →
    ∀ w ∈ budgetWords, ∀ p ∈ UChart,
      wordW w (fun q => ∑' j : ℤ, F j q) p = ∑' j : ℤ, wordW w (F j) p


/-- Component `b ∈ {0,1}` of a meridional pair. -/
def comp2 (v : ℝ × ℝ) (b : Fin 2) : ℝ := if b = 0 then v.1 else v.2

/-- The `(a,b)` Gaussian part of the summand: with `W = A_mer x_j` linear in `A`,
`[V_j, W] = Σ_{a,b} A_{ab} ( (V_j)_b e_a - (x_j)_b ∂_{e_a} V_j )`, indices `a,b ∈ {r,z}` via
`mi`. -/
def hpGaussM (ν : ℝ) (j : ℤ) (a b : Fin 2) : Chart → Merid :=
  fun p => toMer (comp2 (Vj ν p.1 j p.2) b • ei a
    - comp2 (xj ν j p.2) b • fderiv ℝ (Vj ν p.1 j) p.2 (ei a))

/-- The summand is linear in `A^y`: `hpSummandM = Σ_{a,b} A^y_{mi a, mi b}(s) · hpGaussM a b`
(`merApply` expands over the basis; `toMer` is linear). -/
def HpSummandExpand : Prop :=
  ∀ (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ),
    hpSummandM ν χf A j = fun p => ∑ a : Fin 2, ∑ b : Fin 2,
      (Ay ν χf A p.1 (mi a) (mi b)) • hpGaussM ν j a b p

/-- **Assembly**: `HpWordPointwise` from the five lemmas. -/
theorem hpWordPointwise_of (as : ℝ) (χf : ℝ → ℝ)
    (hD : HpSumDecomp) (hS : HpSummandSmooth as χf) (hB : HpSummandBound as χf)
    (hE : EnvSummable) (hL : EnvLocSumm) (hT : TermwiseWord) : HpWordPointwise as χf := by
  intro hχ
  obtain ⟨C, m, hC, H⟩ := hB hχ
  refine ⟨C, 0, m, 1, hC, one_pos, ?_⟩
  intro ν hν _ A hA s hs _ w hw x
  have hM : 0 ≤ affM ν χf A := by
    unfold affM
    exact Real.sSup_nonneg (by
      rintro _ ⟨t, ht, rfl⟩
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _)
        (Finset.sum_nonneg fun _ _ => by unfold frob; exact Real.sqrt_nonneg _))
  have hloc : ∀ w ∈ budgetWords, LocSumm (fun j => wordW w (hpSummandM ν χf A j)) := by
    intro w hw
    refine hL m ν (C * affM ν χf A) hν _ ?_
    intro j p hp
    have := H ν hν A hA p.1 hp.1 w hw p.2 j
    simpa [mul_assoc] using this
  have ht := hT (hpSummandM ν χf A) (hS hχ ν hν A hA) hloc w hw (s, x) ⟨hs, Set.mem_univ _⟩
  have hsum : Summable (fun j : ℤ => C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x)) :=
    (hE m ν hν (s, x) hs).mul_left _
  have hnn : ∀ j : ℤ, ‖wordW w (hpSummandM ν χf A j) (s, x)‖
      ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x) :=
    fun j => H ν hν A hA s hs w hw x j
  have hnsum : Summable (fun j : ℤ => ‖wordW w (hpSummandM ν χf A j) (s, x)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnn hsum
  rw [hD ν χf A, ht]
  calc ‖∑' j : ℤ, wordW w (hpSummandM ν χf A j) (s, x)‖
      ≤ ∑' j : ℤ, ‖wordW w (hpSummandM ν χf A j) (s, x)‖ := norm_tsum_le_tsum_norm hnsum
    _ ≤ ∑' j : ℤ, C * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm m ν j (s, x) :=
        hnsum.tsum_le_tsum hnn hsum
    _ = C * ν⁻¹ ^ 0 * affM ν χf A * s ^ (5 / 2 : ℝ) * latEnv m ν s x := by
        rw [tsum_mul_left]
        simp only [pow_zero, mul_one, latEnv, envTerm]

end UnforcedLeray.Short.PartIIIb.Concrete
