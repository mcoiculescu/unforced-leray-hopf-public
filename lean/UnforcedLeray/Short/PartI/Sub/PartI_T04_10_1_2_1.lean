import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_2
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity

/-!
# Part I, `PartI:T04/10/1/2/1`: the cutoff inequality `APCutoffIneq` through word sums

Source of record: `the November 2 reference manuscript`, lines 285-288
("Approximation and transverse cutoffs then give the velocity and vorticity energy identities.
The scalar vorticity equation ...").

## Why word sums

The vorticity energy identity of lines 285-287 is an identity for the Euclidean jet
`|D^jω|² = Σ_{|u|=j} (∂_uω)²` (`wordSq`; `true` is `∂_q`, `false` is `∂_η`).  With the scalar
vorticity equation `ω_s + v·∇ω = νΔω` and the transverse cutoff `χ_R = etaCutoff R`,
`H_R(s) = ∫_cell χ_R Σ_{|u|=2} (∂_uω(s))²` (`cutoffWordJet c 2 v R`) has
`H_R' = ν ∫χ_R Σ_u 2∂_uω Δ∂_uω - ∫χ_R Σ_u 2∂_uω (v·∇∂_uω) - ∫χ_R Σ_u 2∂_uω [∂_u, v·∇]ω`, and
* viscous term: cell integration by parts against `χ_R` gives
  `-2∫χ_R Σ_{|u|=2}(|∂_q∂_uω|² + |∂_η∂_uω|²) = -2∫χ_R Σ_{|u|=3}(∂_uω)²` plus
  `-2∫χ_R' ∂_uω ∂_η∂_uω = O(1/R)` (`|χ_R'| ≤ C₀/R`, `jet_l2`);
* transport: `-∫χ_R 2g(v·∇g) = ∫χ_R' v_η g² = O(1/R)` (`div v = 0`);
* commutator: `|Σ_{|u|=2} 2∂_uω [∂_u,v·∇]ω| ≤ 16|D²ω|(|D²v||Dω| + 2|Dv||D²ω|)` pointwise, whose
  cell integral is `commJet2`.
The operator norms of `iteratedFDeriv` used by `cutoffVortJet` (sup norm on the plane) satisfy
`‖D^jf‖² ≤ 2^j Σ_{|u|=j}(∂_uf)² ≤ 4^j ‖D^jf‖²` (`WordSqJetCompare`), so integrating in time and
comparing at the endpoints gives `APCutoffIneq` with the constants `16`, `4` and the dissipation
`ν ∫∫χ_R ‖D³ω‖²`.

## Structure

* `cutoffWordCont_of`: continuity of `H_R` on `[0,T]` (proved `CutoffJetContinuous` applied to
  the words frozen at `min t T`; `ClassVortWordCont`).
* `cutoffWordDeriv_of`: `H_R'(r) ≤ -(ν/4) ∫χ_R‖D³ω(r)‖² + commJet2(r) + C/R` on `(0,T)`.
* `apCutoffIneq_of`: time integration (`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`)
  and the endpoint comparisons.

Leaves (all statements about arbitrary smooth functions except the four `Class*` ones, which are
about the class `IsAPrioriClass` of `Sub/T04/Defs.lean`): `WordSqJetCompare`,
`SliceWordTimeCommOn`, `ClassVortWordSmooth`, `ClassVortWordCont`, `ClassVortWordEq`,
`CutoffJetHasDerivOn`, `CutoffViscousL2`, `WordSqSucc`, `CutoffViscousJet`, `CutoffAdvTopL2`,
`CutoffAdvJet`, `CommWord2Expand`, `CommWord2Bound`, `ClassCommIntegrable`.  Already proved and
used as hypotheses: `CutoffJetContinuous`, `CellVortJetIntegrable`, `CurlJetBound`,
`CutoffVortJetMeasurable`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-! ### Vocabulary -/

/-- The squared Euclidean norm of the `j`-th coordinate jet,
`|D^j f(z)|² = Σ_{|u| = j} (∂_u f(z))²` (lines 285-287: the energy identities hold for these sums). -/
def wordSq (j : ℕ) (f : Plane → ℝ) (z : Plane) : ℝ :=
  ∑ u ∈ wordsOfLength j, B0151.derivWord u f z ^ 2

/-- The word-sum cutoff vorticity jet `∫_cell χ_R(η) Σ_{|u| = j} (∂_u ω(s))²`,
`ω = curl v` (lines 285-287, "transverse cutoffs ... vorticity energy identities"). -/
def cutoffWordJet (c : ℝ) (j : ℕ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * wordSq j (Cyl.curl (v s)) z

/-- The density of the commutator majorant: `|D²ω| (|D²u| |Dω| + 2 |Du| |D²ω|)`, `ω = curl u`
(`[∂², u·∇]ω = ∂²u·∇ω + 2∂u·∇∂ω`, lines 285-288); `commJet2 c v r = 16 ∫_cell commDensity (v r)`. -/
def commDensity (u : Plane → Vec) (z : Plane) : ℝ :=
  ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ *
    (‖iteratedFDeriv ℝ 2 u z‖ * ‖iteratedFDeriv ℝ 1 (Cyl.curl u) z‖ +
      2 * (‖iteratedFDeriv ℝ 1 u z‖ * ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖))

theorem commJet2_eq_density (c : ℝ) (v : ℝ → Plane → Vec) (r : ℝ) :
    commJet2 c v r = 16 * ∫ z in Cyl.cell c, commDensity (v r) z := rfl

theorem commDensity_nonneg (u : Plane → Vec) (z : Plane) : 0 ≤ commDensity u z := by
  unfold commDensity
  positivity

/-- `∂_q` of a word derivative is the word with `true` prepended (definitional). -/
theorem partialQ_derivWord (u : List Bool) (f : Plane → ℝ) :
    Cyl.partialQ (B0151.derivWord u f) = B0151.derivWord (true :: u) f := rfl

/-- `∂_η` of a word derivative is the word with `false` prepended (definitional). -/
theorem partialEta_derivWord (u : List Bool) (f : Plane → ℝ) :
    Cyl.partialEta (B0151.derivWord u f) = B0151.derivWord (false :: u) f := rfl

/-- There are `2^j` words of length `j`. -/
theorem card_wordsOfLength (j : ℕ) : (wordsOfLength j).card = 2 ^ j := by
  unfold wordsOfLength
  rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-! ### Leaves: comparison and calculus of words (generic) -/

/-- **Leaf (operator norm versus word sum)** (calculus; `Plane = ℝ × ℝ` with the sup norm).  For
smooth `f`, `‖D^j f(z)‖² ≤ 2^j Σ_{|u|=j}(∂_uf(z))²` and `Σ_{|u|=j}(∂_uf(z))² ≤ 2^j ‖D^jf(z)‖²`.
Route: `cylJetWord_proof` (`Tasks/CylinderInterpolation/JetWord.lean`): every `|∂_uf(z)| ≤ ‖D^jf(z)‖`
for `|u| = j`, and `‖D^jf(z)‖ ≤ Σ_{u ∈ wordsOfLength j} |∂_uf(z)|`; `#wordsOfLength j = 2^j`
(`Finset.card_image_of_injective`, `List.ofFn_injective`, `Fintype.card_fun`); Cauchy-Schwarz
`sq_sum_le_card_mul_sum_sq`. -/
def WordSqJetCompare : Prop :=
  ∀ f : Plane → ℝ, ContDiff ℝ ∞ f → ∀ (j : ℕ) (z : Plane),
    ‖iteratedFDeriv ℝ j f z‖ ^ 2 ≤ 2 ^ j * wordSq j f z ∧
      wordSq j f z ≤ 2 ^ j * ‖iteratedFDeriv ℝ j f z‖ ^ 2

/-- **Leaf (spatial words of a strip-smooth function; `∂_t` through words)** (calculus, lines
276-288 "smooth for positive time").  If `F` is `C^∞` on the open strip `(a,b) × ℝ²`, then every
spatial word `(t,z) ↦ ∂_u[F(t,·)](z)` is `C^∞` there, and for `s ∈ (a,b)`,
`∂_s ∂_u[F(s,·)](z) = ∂_u[∂_sF(s,·)](z)`.  Route: copy
`Tasks/DifferentiatedEnergy/ErrJetL2/VelocityJetL2/EnergyIneq/SliceWordTimeComm.lean` with the open
set `Ioo a b ×ˢ univ` in place of `swtcO = Ioi 0 ×ˢ univ` (`swtcWord`, `swtc_sm`, `swtc_slice`,
`swtc_comm`, `swtc_main`; `LV.lvDir_symm` needs only openness); the first conjunct is
`swtc_sm` plus `ContDiffOn.congr` with `swtc_slice`. -/
def SliceWordTimeCommOn : Prop :=
  ∀ (a b : ℝ) (F : ℝ × Plane → ℝ), ContDiffOn ℝ ∞ F (Ioo a b ×ˢ univ) → ∀ u : List Bool,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => B0151.derivWord u (fun z' => F (x.1, z')) x.2)
      (Ioo a b ×ˢ univ) ∧
    ∀ s ∈ Ioo a b, ∀ z : Plane,
      deriv (fun t => B0151.derivWord u (fun z' => F (t, z')) z) s =
        B0151.derivWord u (fun z' => deriv (fun t => F (t, z')) s) z

/-- **Leaf (differentiation of the cutoff jet energy on a strip)** (measure theory).  If every
`W u` is `C^∞` on `(a,b) × ℝ²`, then at `t₀ ∈ (a,b)` the cutoff jet energy
`t ↦ ∫_cell χ_R Σ_u W u (t,z)²` has derivative `∫_cell χ_R Σ_u 2 W_u ∂_tW_u`.  Route: copy
`cutoffJetHasDeriv_proof` (`.../EnergyIneq/CutoffJetHasDeriv.lean`) with `Ioo a b` in place of
`Ioi 0` and the time window `Icc (t₀ - δ) (t₀ + δ)`, `δ = min (t₀ - a) (b - t₀) / 2`, in place of
`Icc (t₀/2) (2t₀)` (`cjh_deriv_at`, `cjh_cont_G` on the open strip). -/
def CutoffJetHasDerivOn : Prop :=
  ∀ (c R a b : ℝ) (ι : Finset (List Bool)) (W : List Bool → ℝ × Plane → ℝ), 0 < c → 0 < R →
    (∀ u ∈ ι, ContDiffOn ℝ ∞ (W u) (Ioo a b ×ˢ univ)) → ∀ t₀ ∈ Ioo a b,
    HasDerivAt (fun t => ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ ι, W u (t, z) ^ 2)
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        ∑ u ∈ ι, 2 * W u (t₀, z) * deriv (fun t => W u (t, z)) t₀) t₀

/-- **Leaf (viscous term of one function: exact dissipation, `L²` cutoff error)** (lines 286-287).
There is `C₁ ≥ 0` such that for a smooth `c`-periodic `g` with `g², (∂_ηg)²` integrable on the cell
and `R ≥ 1`:
`∫χ_R 2gΔg ≤ -2∫χ_R(|∂_qg|² + |∂_ηg|²) + (C₁/R)(∫g² + ∫(∂_ηg)²)`.
Route: `vi_scalar` (`Tasks/TrainCutoffEnergyProof/ViscousIdentity.lean`; with
`cellIntegrable_of_support`, `cellDerivZero_of_periodic`) gives
`∫χ_R g Δg = -∫χ_R(|∂_qg|² + |∂_ηg|²) - ∫χ_R' g ∂_ηg`; `etaCutoffFacts` gives
`|χ_R'| ≤ (C₀/R)√χ_R ≤ C₀/R`; `2|g ∂_ηg| ≤ g² + (∂_ηg)²`; `C₁ = C₀` (cf. `cjvb_word_bound` in
`.../EnergyIneq/ViscousBound.lean`, which uses sup bounds instead). -/
def CutoffViscousL2 : Prop :=
  ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (c R : ℝ) (g : Plane → ℝ), 0 < c → 1 ≤ R → ContDiff ℝ ∞ g →
    Cyl.IsPeriodic c g → IntegrableOn (fun z => g z ^ 2) (Cyl.cell c) →
    IntegrableOn (fun z => Cyl.partialEta g z ^ 2) (Cyl.cell c) →
    ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * Train.lapS g z) ≤
      -(2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
          (Cyl.partialQ g z ^ 2 + Cyl.partialEta g z ^ 2)) +
        C₁ / R * ((∫ z in Cyl.cell c, g z ^ 2) + ∫ z in Cyl.cell c, Cyl.partialEta g z ^ 2)

/-- **Leaf (re-indexing the dissipation)** (combinatorics of words):
`Σ_{|u|=j}(|∂_q∂_uf|² + |∂_η∂_uf|²) = Σ_{|u'|=j+1}(∂_{u'}f)²`.  Route: `derivWord (true :: u) f`
is `Cyl.partialQ (derivWord u f)` and `derivWord (false :: u) f` is `Cyl.partialEta (derivWord u f)`
by definition (`B0151.derivWord`, `GaussianVortex.partialX`); `wordsOfLength (j+1)` is the
disjoint union of the images of `wordsOfLength j` under `List.cons true` and `List.cons false`
(`List.ofFn_succ`, `Fin.cons`; `Finset.sum_union`, `Finset.sum_image`). -/
def WordSqSucc : Prop :=
  ∀ (f : Plane → ℝ) (j : ℕ) (z : Plane),
    ∑ u ∈ wordsOfLength j, (Cyl.partialQ (B0151.derivWord u f) z ^ 2 +
      Cyl.partialEta (B0151.derivWord u f) z ^ 2) = wordSq (j + 1) f z

/-- **Leaf (viscous term of the order-`j` jet)** (lines 285-287).  For each `j` there is `C₁ ≥ 0`
such that for a smooth `c`-periodic `h` with `‖D^jh‖², ‖D^{j+1}h‖²` integrable on the cell, `R ≥ 1`:
`∫χ_R Σ_{|u|=j} 2∂_uh Δ∂_uh ≤ -2∫χ_R Σ_{|u|=j+1}(∂_uh)² + (C₁/R)(∫‖D^jh‖² + ∫‖D^{j+1}h‖²)`.
Route: `CutoffViscousL2` for each `g = ∂_uh` (smooth: `B0151.contDiff_derivWord`; periodic:
`B0151.periodic_derivWord`), with `g² ≤ ‖D^jh‖²` and `(∂_ηg)² = (∂_{false::u}h)² ≤ ‖D^{j+1}h‖²`
(`cylJetWord_proof`, conjunct 1; integrability by `Integrable.mono'`); sum over the `2^j` words
(`integral_finset_sum`, integrands continuous with `η`-support in `|η| ≤ 2R`:
`vjl_cutoff_integrable`) and `WordSqSucc`; `C₁ = 2^j · C₁(CutoffViscousL2)`. -/
def CutoffViscousJet : Prop :=
  ∀ j : ℕ, ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (c R : ℝ) (h : Plane → ℝ), 0 < c → 1 ≤ R → ContDiff ℝ ∞ h →
    Cyl.IsPeriodic c h →
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ j h z‖ ^ 2) (Cyl.cell c) →
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2) (Cyl.cell c) →
    ∫ z in Cyl.cell c, etaCutoff R z.2 *
        ∑ u ∈ wordsOfLength j, 2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z ≤
      -(2 * ∫ z in Cyl.cell c, etaCutoff R z.2 * wordSq (j + 1) h z) +
        C₁ / R * ((∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2) +
          ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) h z‖ ^ 2)

/-- **Leaf (top transport term of one function, `L²` cutoff error)** (lines 286-287).  There is
`C₂ ≥ 0` such that for a smooth `c`-periodic divergence-free `b` with `|b_η| ≤ M`, a smooth
`c`-periodic `g` with `g²` integrable on the cell, and `R ≥ 1`:
`-∫χ_R 2g(b·∇g) ≤ (C₂/R) M ∫g²`.  Route: as `cutoffAdvTop_proof`
(`.../EnergyIneq/AdvTop.lean`): `tp_core` gives `-∫χ_R 2g(b·∇g) = ∫ g² b_η χ_R'`; then
`|χ_R'| ≤ C₀/R` (`etaCutoffFacts`) and `|b_η| ≤ M` give `|g² b_η χ_R'| ≤ (C₀/R) M g²`, integrate
(`integral_mono`; `g² b_η χ_R'` is continuous with support in `|η| ≤ 2R`); `C₂ = C₀`. -/
def CutoffAdvTopL2 : Prop :=
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (c R M : ℝ) (b : Plane → Vec) (g : Plane → ℝ), 0 < c → 1 ≤ R →
    ContDiff ℝ ∞ b → ContDiff ℝ ∞ g → Cyl.IsPeriodic c b → Cyl.IsPeriodic c g →
    (∀ z : Plane, Cyl.divergence b z = 0) → (∀ z : Plane, |b z 1| ≤ M) →
    IntegrableOn (fun z => g z ^ 2) (Cyl.cell c) →
    -(∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * scalarAdv b g z)) ≤
      C₂ / R * M * ∫ z in Cyl.cell c, g z ^ 2

/-- **Leaf (top transport term of the order-`j` jet)** (lines 286-287).  For each `j` there is
`C₂ ≥ 0` such that for `b` as in `CutoffAdvTopL2`, a smooth `c`-periodic `h` with `‖D^jh‖²`
integrable on the cell, and `R ≥ 1`:
`-∫χ_R Σ_{|u|=j} 2∂_uh (b·∇∂_uh) ≤ (C₂/R) M ∫‖D^jh‖²`.  Route: `CutoffAdvTopL2` for each
`g = ∂_uh`, `(∂_uh)² ≤ ‖D^jh‖²` (`cylJetWord_proof`), `M ≥ 0` (from `|b z 1| ≤ M`), sum over the
`2^j` words (`integral_finset_sum`, `vjl_cutoff_integrable`); `C₂ = 2^j · C₂(CutoffAdvTopL2)`. -/
def CutoffAdvJet : Prop :=
  ∀ j : ℕ, ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (c R M : ℝ) (b : Plane → Vec) (h : Plane → ℝ), 0 < c → 1 ≤ R →
    ContDiff ℝ ∞ b → ContDiff ℝ ∞ h → Cyl.IsPeriodic c b → Cyl.IsPeriodic c h →
    (∀ z : Plane, Cyl.divergence b z = 0) → (∀ z : Plane, |b z 1| ≤ M) →
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ j h z‖ ^ 2) (Cyl.cell c) →
    -(∫ z in Cyl.cell c, etaCutoff R z.2 *
        ∑ u ∈ wordsOfLength j, 2 * B0151.derivWord u h z * scalarAdv b (B0151.derivWord u h) z) ≤
      C₂ / R * M * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j h z‖ ^ 2

/-- **Leaf (the commutator of a length-2 word with the transport, expanded)** (calculus, Leibniz;
lines 285-288: `[∂², v·∇]ω = ∂²v·∇ω + 2∂v·∇∂ω`).  For smooth `b`, `h` and letters `a, a'`:
`∂_a∂_{a'}(b·∇h) - b·∇(∂_a∂_{a'}h) = Σ_k (∂_a∂_{a'}b_k ∂_kh + ∂_ab_k ∂_{a'}∂_kh + ∂_{a'}b_k ∂_a∂_kh)`
(`k = 0 ↔ ∂_q`, `k = 1 ↔ ∂_η`).  Route: `wac_gen` (`.../EnergyIneq/AdvCommutator.lean`) for
`b_0 ∂_qh` and `b_1 ∂_ηh` (`ForcingIBP.derivWord_add_smooth` splits `scalarAdv`); the four
splittings of `[a, a']` (`wacSplits [a, a'] = [([a,a'],[]), ([a],[a']), ([a'],[a]), ([],[a,a'])]`,
by `simp [wacSplits]`); the splitting `([], [a,a'])` is `b_k ∂_{[a,a',k]}h = b_k ∂_{k::[a,a']}h`
(`derivWordConsAppend_proof`), which is the `k`-th term of `scalarAdv b (∂_{[a,a']}h)`. -/
def CommWord2Expand : Prop :=
  ∀ (b : Plane → Vec) (h : Plane → ℝ), ContDiff ℝ ∞ b → ContDiff ℝ ∞ h →
    ∀ (a a' : Bool) (z : Plane),
      B0151.derivWord [a, a'] (scalarAdv b h) z - scalarAdv b (B0151.derivWord [a, a'] h) z =
        (wordComp [a, a'] b 0 z * B0151.derivWord [true] h z +
            wordComp [a] b 0 z * B0151.derivWord [a', true] h z +
            wordComp [a'] b 0 z * B0151.derivWord [a, true] h z) +
          (wordComp [a, a'] b 1 z * B0151.derivWord [false] h z +
            wordComp [a] b 1 z * B0151.derivWord [a', false] h z +
            wordComp [a'] b 1 z * B0151.derivWord [a, false] h z)

/-- **Leaf (pointwise bound of the commutator term)** (lines 285-288).  For smooth `b`, `h`:
`|Σ_{|u|=2} 2∂_uh (∂_u(b·∇h) - b·∇∂_uh)| ≤ 16 |D²h| (|D²b||Dh| + 2|Db||D²h|)`.
Route: `wordsOfLength 2 = {[a,a']}` (four words); `CommWord2Expand`;
`|wordComp w b k z| ≤ ‖D^{|w|}b(z)‖` (`cylJetWord_proof` for `b_k` and
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` with `EuclideanSpace.proj k`, as in
`vjl_wordBoundedOn`) and `|∂_wh(z)| ≤ ‖D^{|w|}h(z)‖` (`cylJetWord_proof`); so each commutator is
`≤ 2|D²b||Dh| + 4|Db||D²h|`, `|∂_uh| ≤ |D²h|`, and `4 · 2 · 2 = 16`. -/
def CommWord2Bound : Prop :=
  ∀ (b : Plane → Vec) (h : Plane → ℝ), ContDiff ℝ ∞ b → ContDiff ℝ ∞ h → ∀ z : Plane,
    |∑ u ∈ wordsOfLength 2, 2 * B0151.derivWord u h z *
        (B0151.derivWord u (scalarAdv b h) z - scalarAdv b (B0151.derivWord u h) z)| ≤
      16 * (‖iteratedFDeriv ℝ 2 h z‖ * (‖iteratedFDeriv ℝ 2 b z‖ * ‖iteratedFDeriv ℝ 1 h z‖ +
        2 * (‖iteratedFDeriv ℝ 1 b z‖ * ‖iteratedFDeriv ℝ 2 h z‖)))

/-! ### Leaves: the class `IsAPrioriClass` -/

/-- **Leaf (smoothness of the vorticity words on the open strip)** (lines 276-288).  For a class
solution and every word `u`, `(t,z) ↦ ∂_u ω(t)(z)` is `C^∞` on `(0,T) × ℝ²`.  Route:
`(t,z) ↦ curl v(t)(z)` is `C^∞` on `(0,T) × ℝ²` (`apcc_curl_smooth` of
`Tasks/TrainGlobalExistence/APLevel2/CutCont.lean` restricted with `ContDiffOn.mono`, or the proof
of `crSmooth` in `Tasks/VorticityFirstMoment/CurlRegularity.lean`, whose `hG'` is the `C^∞`
statement), then `SliceWordTimeCommOn` (first conjunct) with `a = 0`, `b = T`. -/
def ClassVortWordSmooth : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ u : List Bool,
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => B0151.derivWord u (Cyl.curl (v x.1)) x.2)
        (Ioo 0 T ×ˢ univ)

/-- **Leaf (continuity of the vorticity words on the closed strip)** (lines 276-288).  For a class
solution and every word `u`, `(t,z) ↦ ∂_u ω(t)(z)` is continuous on `[0,T] × ℝ²`.  Route:
`∂_uf(z) = D^{|u|}f(z)(e_{u_1}, …)` for smooth `f` (`cjw_word_formula`, `List.ofFn_get`,
`Tasks/CylinderInterpolation/JetWord.lean`), `f = curl v(t)` smooth for `t ∈ [0,T]`
(`APEllipticCaux.curl_contDiff`, `IsClassicalOn.contDiff_slice`); the jets are jointly continuous
on `[0,T] × ℝ²` (`apcc_jet_joint hcls.pos (apcc_curl_smooth hcls.pos hcls.classical.smooth_v)`,
`.../APLevel2/CutCont.lean`), and evaluation at fixed vectors is continuous
(`ContinuousMultilinearMap.apply`). -/
def ClassVortWordCont : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ u : List Bool,
      ContinuousOn (fun x : ℝ × Plane => B0151.derivWord u (Cyl.curl (v x.1)) x.2)
        (Icc 0 T ×ˢ univ)

/-- **Leaf (the differentiated vorticity equation)** (lines 286-288, the scalar vorticity
equation).  For a class solution, `s ∈ (0,T)`, every word `u` and `z`:
`∂_s ∂_uω(s,z) = νΔ∂_uω(s,z) - ∂_u(v·∇ω)(s,z)`.  Route: as `vortWordEquation_proof`
(`.../EnergyIneq/VortWordEquation.lean`) with `TrainSol` replaced by the class: the pointwise
equation `∂_sω = νΔω - v·∇ω` from `localVorticityEquation ν c T v p hν hc hcls.pos hcls.classical`
(`Tasks/VorticityFirstMoment/LocalVorticityEquation.lean`, unfold `B0238.vorticityResidual`);
`SliceWordTimeCommOn` (second conjunct, `a = 0`, `b = T`, `F x = curl v(x.1)(x.2)`, smooth on
`(0,T) × ℝ²` as in `ClassVortWordSmooth`) moves `∂_s` inside `∂_u`; linearity
(`derivWord_sub_smooth`, `vwDerivWord_const_mul`) and `derivWordLapComm_proof`. -/
def ClassVortWordEq : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ s ∈ Ioo (0 : ℝ) T, ∀ (u : List Bool) (z : Plane),
      deriv (fun t => B0151.derivWord u (Cyl.curl (v t)) z) s =
        ν * Train.lapS (B0151.derivWord u (Cyl.curl (v s))) z -
          B0151.derivWord u (scalarAdv (v s) (Cyl.curl (v s))) z

/-- **Leaf (the commutator density is integrable on the cell)** (lines 285-288, `jet_l2`).  For a
class solution and `r ∈ [0,T]`, `z ↦ commDensity (v r) z` is integrable on the cell.  Route:
`commDensity` is continuous (smooth slices, `ContDiff.continuous_iteratedFDeriv`) and, with
`‖D^kv(r)‖ ≤ M_k` (`hcls.bounded`), bounded by
`M₂(‖D²ω‖² + ‖Dω‖²)/2 + 2M₁‖D²ω‖²`, integrable by `cellVortJetIntegrable_proof`
(`Tasks/TrainGlobalExistence/APLevel3/Energy/Limit/CellIntegrable.lean`); `Integrable.mono'`. -/
def ClassCommIntegrable : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ r ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun z => commDensity (v r) z) (Cyl.cell c)

/-! ### Intermediate statements (proved below from the leaves) -/

/-- The word-sum cutoff energy `H_R = cutoffWordJet c 2 v R` is continuous on `[0,T]`. -/
def CutoffWordCont : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (fun t => cutoffWordJet c 2 v R t) (Icc 0 T)

/-- The instantaneous cutoff energy inequality (lines 285-287): there is `C ≥ 0` (depending on
the solution) such that for `R ≥ 1` and `r ∈ (0,T)`, `H_R` is differentiable at `r` with
`H_R'(r) ≤ -(ν/4) ∫χ_R‖D³ω(r)‖² + commJet2(r) + C/R`. -/
def CutoffWordDeriv : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ r ∈ Ioo (0 : ℝ) T,
      ∃ D : ℝ, HasDerivAt (fun t => cutoffWordJet c 2 v R t) D r ∧
        D ≤ -(ν / 4) * cutoffVortJet c 3 v R r + commJet2 c v r + C / R

/-! ### Helpers -/

theorem cwj_wordSq_continuous {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    Continuous (fun z => wordSq j f z) :=
  continuous_finsetSum _ (fun u _ => (B0151.contDiff_derivWord hf u).continuous.pow 2)

theorem cwj_jetSq_continuous {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    Continuous (fun z => ‖iteratedFDeriv ℝ j f z‖ ^ 2) :=
  (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm.pow 2

/-- The two comparisons of `WordSqJetCompare`, weighted by the cutoff and integrated. -/
theorem cwj_cutoff_compare (hW : WordSqJetCompare) {c R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    (∫ z in Cyl.cell c, etaCutoff R z.2 * ‖iteratedFDeriv ℝ j f z‖ ^ 2) ≤
        2 ^ j * ∫ z in Cyl.cell c, etaCutoff R z.2 * wordSq j f z ∧
      (∫ z in Cyl.cell c, etaCutoff R z.2 * wordSq j f z) ≤
        2 ^ j * ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖iteratedFDeriv ℝ j f z‖ ^ 2 := by
  have i1 := vjl_cutoff_integrable (c := c) hR (cwj_jetSq_continuous hf j)
  have i2 := vjl_cutoff_integrable (c := c) hR (cwj_wordSq_continuous hf j)
  constructor
  · rw [← integral_const_mul]
    refine integral_mono i1 (i2.const_mul _) (fun z => ?_)
    have h := (hW f hf j z).1
    have h0 := etaCutoff_nonneg R z.2
    show etaCutoff R z.2 * ‖iteratedFDeriv ℝ j f z‖ ^ 2 ≤
      2 ^ j * (etaCutoff R z.2 * wordSq j f z)
    calc etaCutoff R z.2 * ‖iteratedFDeriv ℝ j f z‖ ^ 2
        ≤ etaCutoff R z.2 * (2 ^ j * wordSq j f z) := mul_le_mul_of_nonneg_left h h0
      _ = 2 ^ j * (etaCutoff R z.2 * wordSq j f z) := by ring
  · rw [← integral_const_mul]
    refine integral_mono i2 (i1.const_mul _) (fun z => ?_)
    have h := (hW f hf j z).2
    have h0 := etaCutoff_nonneg R z.2
    show etaCutoff R z.2 * wordSq j f z ≤
      2 ^ j * (etaCutoff R z.2 * ‖iteratedFDeriv ℝ j f z‖ ^ 2)
    calc etaCutoff R z.2 * wordSq j f z
        ≤ etaCutoff R z.2 * (2 ^ j * ‖iteratedFDeriv ℝ j f z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h h0
      _ = 2 ^ j * (etaCutoff R z.2 * ‖iteratedFDeriv ℝ j f z‖ ^ 2) := by ring

/-- Uniform bound of `‖D^jω(r)‖²₂` on `[0,T]` for a class solution (`jet_l2`, `CurlJetBound`). -/
theorem cwj_vortJet_bound (hCB : CurlJetBound) (hI : CellVortJetIntegrable) {ν c T : ℝ}
    {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (hcls : IsAPrioriClass ν c T v p) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Icc (0 : ℝ) T, vortJet c j v r ≤ K := by
  obtain ⟨C, _hC0, hC⟩ := hCB j
  obtain ⟨K, hK⟩ := hcls.jet_l2 (j + 1)
  refine ⟨C ^ 2 * max K 0, by positivity, fun r hr => ?_⟩
  have hsm := hcls.classical.contDiff_slice hr
  have hint := hI ν c T v p hν hc hcls r hr j
  obtain ⟨hiv, hKv⟩ := hK r hr
  unfold vortJet
  calc ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl (v r)) z‖ ^ 2
      ≤ ∫ z in Cyl.cell c, C ^ 2 * ‖iteratedFDeriv ℝ (j + 1) (v r) z‖ ^ 2 := by
        refine integral_mono hint (hiv.const_mul _) (fun z => ?_)
        have h1 := hC (v r) hsm z
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        rw [mul_pow] at h2
        exact h2
    _ = C ^ 2 * velJet c (j + 1) v r := integral_const_mul _ _
    _ ≤ C ^ 2 * max K 0 :=
        mul_le_mul_of_nonneg_left (hKv.trans (le_max_left _ _)) (sq_nonneg _)

theorem cwj_sum_alg (ι : Finset (List Bool)) (χ ν : ℝ) (a l d t : List Bool → ℝ) :
    χ * ∑ u ∈ ι, 2 * a u * (ν * l u - d u) =
      ν * (χ * ∑ u ∈ ι, 2 * a u * l u) - χ * ∑ u ∈ ι, 2 * a u * t u -
        χ * ∑ u ∈ ι, 2 * a u * (d u - t u) := by
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun u _ => by ring)

/-! ### Continuity of the word-sum cutoff energy -/

/-- **`CutoffWordCont`** from `CutoffJetContinuous` (proved, for words continuous on
`[0,∞) × ℝ²`) applied to the words frozen at `min t T`. -/
theorem cutoffWordCont_of (hCont : CutoffJetContinuous) (hWc : ClassVortWordCont) :
    CutoffWordCont := by
  intro ν c T v p hν hc hcls R hR
  have hc0 : 0 < c := by linarith
  have hR0 : 0 < R := by linarith
  have hT := hcls.pos
  have hW' : ∀ u ∈ wordsOfLength 2, ContinuousOn
      (fun x : ℝ × Plane => B0151.derivWord u (Cyl.curl (v (min x.1 T))) x.2)
      (Ici 0 ×ˢ univ) := by
    intro u _
    have h := hWc ν c T v p hν hc hcls u
    have hf : ContinuousOn (fun x : ℝ × Plane => ((min x.1 T, x.2) : ℝ × Plane))
        (Ici 0 ×ˢ univ) :=
      ((continuous_fst.min continuous_const).prodMk continuous_snd).continuousOn
    have hmaps : MapsTo (fun x : ℝ × Plane => ((min x.1 T, x.2) : ℝ × Plane))
        (Ici 0 ×ˢ univ) (Icc 0 T ×ˢ univ) := fun x hx =>
      ⟨⟨le_min hx.1 hT.le, min_le_right _ _⟩, mem_univ _⟩
    exact h.comp hf hmaps
  have key := hCont c R T (wordsOfLength 2)
    (fun u x => B0151.derivWord u (Cyl.curl (v (min x.1 T))) x.2) hc0 hR0 hW'
  refine key.congr (fun t ht => ?_)
  show cutoffWordJet c 2 v R t = ∫ z in Cyl.cell c, etaCutoff R z.2 *
    ∑ u ∈ wordsOfLength 2, B0151.derivWord u (Cyl.curl (v (min t T))) z ^ 2
  rw [min_eq_left ht.2]
  rfl

/-! ### The instantaneous inequality -/

/-- **`CutoffWordDeriv`** from the leaves. -/
theorem cutoffWordDeriv_of (hSm : ClassVortWordSmooth) (hEq : ClassVortWordEq)
    (hDer : CutoffJetHasDerivOn) (hVisc : CutoffViscousJet) (hAdv : CutoffAdvJet)
    (hCom : CommWord2Bound) (hCI : ClassCommIntegrable) (hW : WordSqJetCompare)
    (hI : CellVortJetIntegrable) (hCB : CurlJetBound) : CutoffWordDeriv := by
  intro ν c T v p hν hc hcls
  have hc0 : 0 < c := by linarith
  obtain ⟨C₁, hC₁, hV⟩ := hVisc 2
  obtain ⟨C₂, hC₂, hA⟩ := hAdv 2
  obtain ⟨K₂, hK₂, hY2⟩ := cwj_vortJet_bound hCB hI hν hc hcls 2
  obtain ⟨K₃, hK₃, hY3⟩ := cwj_vortJet_bound hCB hI hν hc hcls 3
  obtain ⟨M, hM⟩ := hcls.bounded 0
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hcls.pos.le⟩ 0)
  refine ⟨ν * C₁ * (K₂ + K₃) + C₂ * M * K₂, by positivity, fun R hR r hr => ?_⟩
  have hR0 : 0 < R := by linarith
  have hrI : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
  have hv : ContDiff ℝ ∞ (v r) := hcls.classical.contDiff_slice hrI
  have hω : ContDiff ℝ ∞ (Cyl.curl (v r)) := APEllipticCaux.curl_contDiff hv
  have hωp : Cyl.IsPeriodic c (Cyl.curl (v r)) := crPeriodic hcls.classical.periodic_v hrI
  have hvp : Cyl.IsPeriodic c (v r) := hcls.classical.periodic_v r hrI
  have hdiv : ∀ z, Cyl.divergence (v r) z = 0 := hcls.classical.solenoidal r hrI
  have hv1 : ∀ z, |v r z 1| ≤ M := fun z => by
    have h1 := hM r hrI z
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 : |v r z 1| ≤ ‖v r z‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (v r z) 1
    exact h2.trans h1
  -- the derivative of the word-sum cutoff energy
  have hd : HasDerivAt (fun t => cutoffWordJet c 2 v R t)
      (∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
        2 * B0151.derivWord u (Cyl.curl (v r)) z *
          deriv (fun t => B0151.derivWord u (Cyl.curl (v t)) z) r) r :=
    hDer c R 0 T (wordsOfLength 2) (fun u x => B0151.derivWord u (Cyl.curl (v x.1)) x.2)
      hc0 hR0 (fun u _ => hSm ν c T v p hν hc hcls u) r hr
  refine ⟨_, hd, ?_⟩
  -- the three pieces of the integrand
  have hg : ∀ u : List Bool, ContDiff ℝ ∞ (B0151.derivWord u (Cyl.curl (v r))) :=
    fun u => B0151.contDiff_derivWord hω u
  have hadv : ContDiff ℝ ∞ (scalarAdv (v r) (Cyl.curl (v r))) := vjl_scalarAdv_contDiff hv hω
  have c1 : Continuous (fun z => ∑ u ∈ wordsOfLength 2, 2 * B0151.derivWord u (Cyl.curl (v r)) z *
      Train.lapS (B0151.derivWord u (Cyl.curl (v r))) z) :=
    continuous_finsetSum _ (fun u _ =>
      (continuous_const.mul (hg u).continuous).mul (vjl_lapS_contDiff (hg u)).continuous)
  have c2 : Continuous (fun z => ∑ u ∈ wordsOfLength 2, 2 * B0151.derivWord u (Cyl.curl (v r)) z *
      scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z) :=
    continuous_finsetSum _ (fun u _ =>
      (continuous_const.mul (hg u).continuous).mul (vjl_scalarAdv_contDiff hv (hg u)).continuous)
  have c3 : Continuous (fun z => ∑ u ∈ wordsOfLength 2, 2 * B0151.derivWord u (Cyl.curl (v r)) z *
      (B0151.derivWord u (scalarAdv (v r) (Cyl.curl (v r))) z -
        scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z)) :=
    continuous_finsetSum _ (fun u _ =>
      (continuous_const.mul (hg u).continuous).mul
        ((B0151.contDiff_derivWord hadv u).continuous.sub
          (vjl_scalarAdv_contDiff hv (hg u)).continuous))
  have i1 := vjl_cutoff_integrable (c := c) hR0 c1
  have i2 := vjl_cutoff_integrable (c := c) hR0 c2
  have i3 := vjl_cutoff_integrable (c := c) hR0 c3
  have hfun : (fun z : Plane => etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
        2 * B0151.derivWord u (Cyl.curl (v r)) z *
          deriv (fun t => B0151.derivWord u (Cyl.curl (v t)) z) r) =
      fun z => ν * (etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
          2 * B0151.derivWord u (Cyl.curl (v r)) z *
            Train.lapS (B0151.derivWord u (Cyl.curl (v r))) z) -
        etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2, 2 * B0151.derivWord u (Cyl.curl (v r)) z *
          scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z -
        etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2, 2 * B0151.derivWord u (Cyl.curl (v r)) z *
          (B0151.derivWord u (scalarAdv (v r) (Cyl.curl (v r))) z -
            scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z) := by
    funext z
    rw [Finset.sum_congr rfl (fun u _ => by rw [hEq ν c T v p hν hc hcls r hr u z])]
    exact cwj_sum_alg _ _ _ _ _ _ _
  have i12 : Integrable (fun z : Plane => ν * (etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
          2 * B0151.derivWord u (Cyl.curl (v r)) z *
            Train.lapS (B0151.derivWord u (Cyl.curl (v r))) z) -
        etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2, 2 * B0151.derivWord u (Cyl.curl (v r)) z *
          scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z)
      (volume.restrict (Cyl.cell c)) := (i1.const_mul ν).sub i2
  rw [hfun, integral_sub i12 i3, integral_sub (i1.const_mul ν) i2, integral_const_mul]
  -- viscous term
  have hint2 := hI ν c T v p hν hc hcls r hrI 2
  have hint3 := hI ν c T v p hν hc hcls r hrI 3
  have bV : ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
        2 * B0151.derivWord u (Cyl.curl (v r)) z *
          Train.lapS (B0151.derivWord u (Cyl.curl (v r))) z ≤
      -(2 * cutoffWordJet c 3 v R r) + C₁ / R * (vortJet c 2 v r + vortJet c 3 v r) :=
    hV c R (Cyl.curl (v r)) hc0 hR hω hωp hint2 hint3
  -- transport term
  have bA : -(∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
        2 * B0151.derivWord u (Cyl.curl (v r)) z *
          scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z) ≤
      C₂ / R * M * vortJet c 2 v r :=
    hA c R M (v r) (Cyl.curl (v r)) hc0 hR hv hω hvp hωp hdiv hv1 hint2
  -- commutator term
  have hcdc : Continuous (fun z => commDensity (v r) z) := by
    unfold commDensity
    have e2 := (hω.continuous_iteratedFDeriv (m := 2) (by simp)).norm
    have e1 := (hω.continuous_iteratedFDeriv (m := 1) (by simp)).norm
    have f2 := (hv.continuous_iteratedFDeriv (m := 2) (by simp)).norm
    have f1 := (hv.continuous_iteratedFDeriv (m := 1) (by simp)).norm
    exact e2.mul ((f2.mul e1).add (continuous_const.mul (f1.mul e2)))
  have i4 := vjl_cutoff_integrable (c := c) hR0 (continuous_const.mul hcdc :
    Continuous (fun z => 16 * commDensity (v r) z))
  have bC : -(∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
        2 * B0151.derivWord u (Cyl.curl (v r)) z *
          (B0151.derivWord u (scalarAdv (v r) (Cyl.curl (v r))) z -
            scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z)) ≤ commJet2 c v r := by
    rw [← integral_neg, commJet2_eq_density, ← integral_const_mul]
    calc ∫ z in Cyl.cell c, -(etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
          2 * B0151.derivWord u (Cyl.curl (v r)) z *
            (B0151.derivWord u (scalarAdv (v r) (Cyl.curl (v r))) z -
              scalarAdv (v r) (B0151.derivWord u (Cyl.curl (v r))) z))
        ≤ ∫ z in Cyl.cell c, etaCutoff R z.2 * (16 * commDensity (v r) z) := by
          refine integral_mono i3.neg i4 (fun z => ?_)
          have h := hCom (v r) (Cyl.curl (v r)) hv hω z
          have h0 := etaCutoff_nonneg R z.2
          have h' := (neg_le_abs _).trans h
          have h'' := mul_le_mul_of_nonneg_left h' h0
          show -(etaCutoff R z.2 * _) ≤ etaCutoff R z.2 * (16 * commDensity (v r) z)
          unfold commDensity
          linarith
      _ ≤ ∫ z in Cyl.cell c, 16 * commDensity (v r) z := by
          refine integral_mono i4 ((hCI ν c T v p hν hc hcls r hrI).const_mul 16) (fun z => ?_)
          have h1 := cehd_eta_le_one R z.2
          have hn : 0 ≤ 16 * commDensity (v r) z := by
            have := commDensity_nonneg (v r) z
            positivity
          show etaCutoff R z.2 * (16 * commDensity (v r) z) ≤ 16 * commDensity (v r) z
          nlinarith
  -- dissipation comparison
  have bW : cutoffVortJet c 3 v R r ≤ 8 * cutoffWordJet c 3 v R r := by
    have h := (cwj_cutoff_compare hW (c := c) hR0 hω 3).1
    norm_num at h
    exact h
  have hy2 := hY2 r hrI
  have hy3 := hY3 r hrI
  have hCR1 : 0 ≤ C₁ / R := div_nonneg hC₁ hR0.le
  have hCR2 : 0 ≤ C₂ / R * M := mul_nonneg (div_nonneg hC₂ hR0.le) hM0
  have ha : ν * (∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsOfLength 2,
        2 * B0151.derivWord u (Cyl.curl (v r)) z *
          Train.lapS (B0151.derivWord u (Cyl.curl (v r))) z) ≤
      ν * (-(2 * cutoffWordJet c 3 v R r) + C₁ / R * (vortJet c 2 v r + vortJet c 3 v r)) :=
    mul_le_mul_of_nonneg_left bV hν.le
  have hb : ν * (C₁ / R * (vortJet c 2 v r + vortJet c 3 v r)) ≤ ν * (C₁ / R * (K₂ + K₃)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hCR1) hν.le
  have hc' : C₂ / R * M * vortJet c 2 v r ≤ C₂ / R * M * K₂ :=
    mul_le_mul_of_nonneg_left hy2 hCR2
  have hd' : ν * cutoffVortJet c 3 v R r ≤ ν * (8 * cutoffWordJet c 3 v R r) :=
    mul_le_mul_of_nonneg_left bW hν.le
  have e : (ν * C₁ * (K₂ + K₃) + C₂ * M * K₂) / R =
      ν * (C₁ / R * (K₂ + K₃)) + C₂ / R * M * K₂ := by ring
  rw [e]
  nlinarith [ha, hb, hc', hd', bA, bC]

/-! ### The cutoff inequality -/

/-- **`APCutoffIneq` from the instantaneous inequality** (time integration and the endpoint
comparisons of word sums with operator norms). -/
theorem apCutoffIneq_of (hD : CutoffWordDeriv) (hC : CutoffWordCont) (hW : WordSqJetCompare)
    (hI : CellVortJetIntegrable) (hM : CutoffVortJetMeasurable) : APCutoffIneq := by
  intro ν c T v p hν hc hcls h3 hCI
  obtain ⟨C, hC0, hDer⟩ := hD ν c T v p hν hc hcls
  refine ⟨fun R => 4 * T * C / R, tendsto_const_nhds.div_atTop tendsto_id, fun R hR s hs => ?_⟩
  have hR0 : 0 < R := by linarith
  have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hs.2
  -- the cutoff dissipation is integrable on `[0,T]`
  have hcv3 : IntegrableOn (fun r => cutoffVortJet c 3 v R r) (Icc (0 : ℝ) T) := by
    refine Integrable.mono' h3 (hM ν c T v p hν hc hcls 3 R) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
    have hint := hI ν c T v p hν hc hcls r hr 3
    have hnn : 0 ≤ cutoffVortJet c 3 v R r :=
      integral_nonneg fun z => mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    unfold cutoffVortJet vortJet
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _)) hint
      (Eventually.of_forall fun z => by
        have h1 := cehd_eta_le_one R z.2
        have hb : 0 ≤ ‖iteratedFDeriv ℝ 3 (Cyl.curl (v r)) z‖ ^ 2 := sq_nonneg _
        show etaCutoff R z.2 * ‖iteratedFDeriv ℝ 3 (Cyl.curl (v r)) z‖ ^ 2 ≤
          ‖iteratedFDeriv ℝ 3 (Cyl.curl (v r)) z‖ ^ 2
        nlinarith)
  have hφint : IntegrableOn (fun r => -(ν / 4) * cutoffVortJet c 3 v R r + commJet2 c v r +
      C / R) (Icc (0 : ℝ) s) :=
    (((hcv3.mono_set hsub).const_mul (-(ν / 4))).add (hCI.mono_set hsub)).add
      (integrableOn_const measure_Icc_lt_top.ne)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) s, HasDerivWithinAt (fun t => cutoffWordJet c 2 v R t)
      (deriv (fun t => cutoffWordJet c 2 v R t) x) (Ioi x) x := by
    intro x hx
    obtain ⟨D, hDx, -⟩ := hDer R hR x ⟨hx.1, hx.2.trans_le hs.2⟩
    rw [hDx.deriv]
    exact hDx.hasDerivWithinAt
  have hle : ∀ x ∈ Ioo (0 : ℝ) s, deriv (fun t => cutoffWordJet c 2 v R t) x ≤
      -(ν / 4) * cutoffVortJet c 3 v R x + commJet2 c v x + C / R := by
    intro x hx
    obtain ⟨D, hDx, hDle⟩ := hDer R hR x ⟨hx.1, hx.2.trans_le hs.2⟩
    rw [hDx.deriv]
    exact hDle
  have hFTC := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hs.1
    ((hC ν c T v p hν hc hcls R hR).mono hsub) hderiv hφint hle
  have hiv := intervalIntegrable_of_integrableOn_Icc hcv3 hs
  have hiC := intervalIntegrable_of_integrableOn_Icc hCI hs
  have hφeq : ∫ r in (0 : ℝ)..s, (-(ν / 4) * cutoffVortJet c 3 v R r + commJet2 c v r + C / R) =
      -(ν / 4) * (∫ r in (0 : ℝ)..s, cutoffVortJet c 3 v R r) +
        (∫ r in (0 : ℝ)..s, commJet2 c v r) + s * (C / R) := by
    rw [intervalIntegral.integral_add ((hiv.const_mul _).add hiC) intervalIntegrable_const,
      intervalIntegral.integral_add (hiv.const_mul _) hiC, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [hφeq] at hFTC
  -- endpoint comparisons
  have hs0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hcls.pos.le⟩
  have hωs : ContDiff ℝ ∞ (Cyl.curl (v s)) :=
    APEllipticCaux.curl_contDiff (hcls.classical.contDiff_slice hs)
  have hω0 : ContDiff ℝ ∞ (Cyl.curl (v 0)) :=
    APEllipticCaux.curl_contDiff (hcls.classical.contDiff_slice hs0)
  have hcs : cutoffVortJet c 2 v R s ≤ 4 * cutoffWordJet c 2 v R s := by
    have h := (cwj_cutoff_compare hW (c := c) hR0 hωs 2).1
    norm_num at h
    exact h
  have hc0' : cutoffWordJet c 2 v R 0 ≤ 4 * cutoffVortJet c 2 v R 0 := by
    have h := (cwj_cutoff_compare hW (c := c) hR0 hω0 2).2
    norm_num at h
    exact h
  have hsT : s * (C / R) ≤ T * (C / R) :=
    mul_le_mul_of_nonneg_right hs.2 (div_nonneg hC0 hR0.le)
  have e : 4 * T * C / R = 4 * (T * (C / R)) := by ring
  beta_reduce
  rw [e]
  linarith [hFTC, hcs, hc0', hsT]

end UnforcedLeray.Short.PartI
