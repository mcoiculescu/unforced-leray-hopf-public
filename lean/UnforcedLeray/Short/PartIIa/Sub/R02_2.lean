import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part II-a, task `PartII-a:R02/2`: the fluctuation profile bounds (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`) and 1259-1276 (late residual table).

Target: `LateFluctuationProfile` (`Sub/R02.lean`): for fixed `ρ, m, a, b, ℓ`,
`(1+η²/s)^m |K^ℓ ∂_η^a ∂_q^b f| ≤ P e^{-κνs/c²}` for `s ≥ 1`, `f = ψ̃` or `f = p`.


partials `∂_η, ∂_q, ∂_s, K` of `trainProfile F` to the jets `ageJet` of `TrainFluctuationDecay`.
This file cuts the target into

* the profile calculus (shared with `PartII-a:R02/3` and `PartII-a:R02/6`, which import this file):
  `ProfileIterComm` (the partials `∂_η, ∂_q, ∂_s` commute on functions that are `C^∞` for `s > 0`),
  `KExpansion` (`K^ℓ = ∑ n_{ik} η^i s^k ∂_η^i ∂_s^k`), `ProfileDict` (the profile partials of
  `trainProfile F` are nested `iteratedDeriv`s of `F`), `SliceJetBound` (a nested slice derivative
  is bounded by the operator norm of the corresponding `ageJet`; with `ProfileDict` this gives
  `ProfileJetBound`, `profileJetBound_of`), `ExpPowAbsorb` (`s^k e^{-A s} ≤ P e^{-A s/2}`), and
  `FluctProfileSmooth` (smoothness of `ψ̃`);
* the generic finite assembly `late_assembly` (proved here, no hypothesis on the train): if every
  term `(1+η²/s)^m |η|^i s^k |∂_η^{i+a} ∂_q^b ∂_s^k G|` has a bound of the form
  `polyConst C N ν c · D κ` then so has `(1+η²/s)^m |K^ℓ ∂_η^a ∂_q^b G|`;
* the term bound `fluctTermBound_of` (proved here from `TrainFluctuationDecay`, `ProfileJetBound`,
  `ExpPowAbsorb`, `FluctProfileSmooth`): the weight `(1+η²/s)^m |η|^i ≤ (1+η²)^{m+i}` for `s ≥ 1`
  is absorbed by the weighted sup norm with `m' = 2(m+i)`, and the factor `s^k` by halving `κ`.

`lateFluctuationProfile_of_sub` below is the conditional theorem; the unconditional statement
`lateFluctuationProfile_of (hF) (hS) : LateFluctuationProfile` is the task file
`Short/PartII-a/Tasks/R02/FluctuationProfile.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream ageJet)

/-! ### Profile calculus (leaves) -/

/-- **Commutation of the profile partials** (calculus; `∂_η, ∂_q, ∂_s` commute on functions that
are `C^∞` on the open set `{s > 0}`, by the symmetry of second derivatives of a `C²` function): for
`G` smooth for `s > 0`, at every point with `s > 0`,
`∂_η^i ∂_s^k ∂_η^a ∂_q^b G = ∂_η^{i+a} ∂_q^b ∂_s^k G`. -/
def ProfileIterComm : Prop :=
  ∀ G : ProfilePoint → ℝ, ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2} →
    ∀ (i a b k : ℕ) (x : ProfilePoint), 0 < x.2.2 →
      (partialEta^[i] (partialAge^[k] (partialEta^[a] (partialQ^[b] G)))) x =
        (partialEta^[i + a] (partialQ^[b] (partialAge^[k] G))) x

/-- **Expansion of `K^ℓ`** (`K = η∂_η + 2s∂_s`, `ageOperator`; source lines 439-446, step (i) of
the route): there are real numbers `n_{ik}` (nonnegative integers in fact, depending only on `ℓ`)
with `K^ℓ G = ∑_{i,k ≤ ℓ} n_{ik} η^i s^k ∂_η^i ∂_s^k G` at every point with `s > 0`, for every `G`
that is `C^∞` for `s > 0`.  (Induction on `ℓ`:
`K(η^i s^k ∂_η^i∂_s^k G) = (i+2k) η^i s^k ∂_η^i∂_s^k G + η^{i+1} s^k ∂_η^{i+1}∂_s^k G +
2 η^i s^{k+1} ∂_η^i∂_s^{k+1} G`, using `∂_η∂_s = ∂_s∂_η`.) -/
def KExpansion : Prop :=
  ∀ ℓ : ℕ, ∃ n : ℕ → ℕ → ℝ, ∀ G : ProfilePoint → ℝ,
    ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2} → ∀ x : ProfilePoint, 0 < x.2.2 →
      (ageOperator^[ℓ] G) x = ∑ i ∈ Finset.range (ℓ + 1), ∑ k ∈ Finset.range (ℓ + 1),
        n i k * x.2.1 ^ i * x.2.2 ^ k * (partialEta^[i] (partialAge^[k] G)) x

/-- **Profile partials are nested slice derivatives** (calculus): for a train-type field
`F(s, (q, η))` whose profile `(q, η, s) ↦ F(s, (q, η))` is `C^∞` for `s > 0`, at every point with
`s > 0`, `∂_η^a ∂_q^b ∂_s^k (trainProfile F)` at `(q, η, s)` is the `a`-th derivative in `η` of the
`b`-th derivative in `q` of the `k`-th derivative in the age of `F`.  (`∂_s^k` of the profile is
`iteratedDeriv k (fun r => F r z) s` because the profile is `C^∞` along the age line; the same
for `∂_q^b` and `∂_η^a` applied to the resulting `C^∞` function.) -/
def ProfileDict : Prop :=
  ∀ F : ℝ → ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ (trainProfile F) {y : ProfilePoint | 0 < y.2.2} →
    ∀ (a b k : ℕ) (x : ProfilePoint), 0 < x.2.2 →
      (partialEta^[a] (partialQ^[b] (partialAge^[k] (trainProfile F)))) x =
        iteratedDeriv a (fun e => iteratedDeriv b
          (fun q' => iteratedDeriv k (fun r => F r (q', e)) x.2.2) x.1) x.2.1

/-- **Nested slice derivatives are bounded by jets** (step (ii) of the route): with `F` as above,
the nested derivative `∂_η^a ∂_q^b ∂_s^k F` at `(q, η, s)` is bounded by the operator norm of
`ageJet k (a+b) F s (q, η) = D^{a+b}(∂_s^k F(s))(q, η)` (evaluate `D^{a+b}` on `a` copies of
`(0,1)` and `b` copies of `(1,0)`, all of norm `1` in `ℝ × ℝ`). -/
def SliceJetBound : Prop :=
  ∀ F : ℝ → ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ (trainProfile F) {y : ProfilePoint | 0 < y.2.2} →
    ∀ (a b k : ℕ) (q η s : ℝ), 0 < s →
      |iteratedDeriv a (fun e => iteratedDeriv b
          (fun q' => iteratedDeriv k (fun r => F r (q', e)) s) q) η| ≤
        ‖ageJet k (a + b) F s (q, η)‖

/-- **Profile partials are bounded by jets** (steps (i)-(ii) of the route); derived from
`ProfileDict` and `SliceJetBound` below (`profileJetBound_of`). -/
def ProfileJetBound : Prop :=
  ∀ F : ℝ → ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ (trainProfile F) {y : ProfilePoint | 0 < y.2.2} →
    ∀ (a b k : ℕ) (x : ProfilePoint), 0 < x.2.2 →
      |(partialEta^[a] (partialQ^[b] (partialAge^[k] (trainProfile F)))) x| ≤
        ‖ageJet k (a + b) F x.2.2 (x.1, x.2.1)‖

/-- **Age derivatives of jointly smooth functions are jointly smooth** (calculus; used by the
leaves of `R02/3` and `R02/6`): if `f(s, w)` is `C^∞` on the open set `(0,∞) × E`, then so is
`(s, w) ↦ ∂_s^k f(s, w) = iteratedDeriv k (fun r => f r w) s`, for `E = ℝ` and `E = ℝ × ℝ`.
(Induction on `k`: on the open set `∂_s h (s, w) = fderiv ℝ h (s, w) (1, 0)`, and the derivative of a
`C^∞` function applied to a constant vector is `C^∞`: `ContDiffOn.fderiv_of_isOpen`,
`ContDiffOn.clm_apply`.) -/
def AgeDerivSmooth : Prop :=
  (∀ f : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => f x.1 x.2) (Ioi 0 ×ˢ univ) → ∀ k : ℕ,
      ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (fun r => f r x.2) x.1)
        (Ioi 0 ×ˢ univ)) ∧
  (∀ f : ℝ → ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ k : ℕ, ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => iteratedDeriv k (fun r => f r x.2) x.1)
      (Ioi 0 ×ˢ univ))

/-- **Absorbing a power of the age into the exponential** (elementary; `s^k e^{-A s} ≤ k! (2/A)^k
e^{-A s/2}` from `x^k/k! ≤ e^x`, with `A = κν/c²` and `(2/A)^k ≤ (2/κ)^k (1+c+ν⁻¹)^{3k}`): halving
`κ` absorbs `s^k`, at the price of a polynomial in `c, ν⁻¹`. -/
def ExpPowAbsorb : Prop :=
  ∀ (κ : ℝ) (k : ℕ), 0 < κ → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s →
      s ^ k * Real.exp (-(κ * ν * s / c ^ 2)) ≤
        polyConst C N ν c * Real.exp (-(κ / 2 * ν * s / c ^ 2))

/-- **Smoothness of the stream fluctuation** (source lines 397-404 and 439-446): the profile
`ψ̃(q, η, s) = ψ(s, (q, η)) - S(s, η)` of the fluctuation of the stream is `C^∞` for `s > 0`
(`S = \bar ψ` is `C^∞` by `HmeanContDiff`, `PartI/Sub/T01.lean`, proved as `hmeanContDiff` in
`Short/PartI/Tasks/TrainMeanEquations/HmeanContDiff.lean`).  Proved from `LateProfileSmooth` and
`HmeanContDiff` by the task `PartII-a:R02/2/5`. -/
def FluctProfileSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ContDiffOn ℝ ∞ (trainProfile fun s z => tr.ψ s z - meanStream tr s z.2)
      {y : ProfilePoint | 0 < y.2.2}

/-! ### Elementary lemmas -/

theorem isOpen_late : IsOpen {y : ProfilePoint | 0 < y.2.2} :=
  isOpen_lt continuous_const (continuous_snd.comp continuous_snd)

theorem contDiffOn_fderiv_apply {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (v : ProfilePoint) :
    ContDiffOn ℝ ∞ (fun y => fderiv ℝ G y v) {y : ProfilePoint | 0 < y.2.2} :=
  (hG.fderiv_of_isOpen isOpen_late (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_iterate (D : (ProfilePoint → ℝ) → (ProfilePoint → ℝ))
    (hD : ∀ G, ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2} →
      ContDiffOn ℝ ∞ (D G) {y : ProfilePoint | 0 < y.2.2})
    {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (n : ℕ) :
    ContDiffOn ℝ ∞ (D^[n] G) {y : ProfilePoint | 0 < y.2.2} := by
  induction n with
  | zero => simpa using hG
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hD _ ih

theorem contDiffOn_partialEta_iter {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (a : ℕ) :
    ContDiffOn ℝ ∞ (partialEta^[a] G) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_iterate partialEta (fun _ h => contDiffOn_fderiv_apply h eηDir) hG a

theorem contDiffOn_partialQ_iter {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (b : ℕ) :
    ContDiffOn ℝ ∞ (partialQ^[b] G) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_iterate partialQ (fun _ h => contDiffOn_fderiv_apply h eqDir) hG b

theorem le_double_sum_real {r : Finset ℕ} {f : ℕ → ℕ → ℝ} (hf : ∀ i k, 0 ≤ f i k) {i k : ℕ}
    (hi : i ∈ r) (hk : k ∈ r) : f i k ≤ ∑ i ∈ r, ∑ k ∈ r, f i k :=
  calc f i k ≤ ∑ k' ∈ r, f i k' := Finset.single_le_sum (fun k' _ => hf i k') hk
    _ ≤ ∑ i ∈ r, ∑ k ∈ r, f i k :=
      Finset.single_le_sum (f := fun i => ∑ k ∈ r, f i k)
        (fun i _ => Finset.sum_nonneg fun k _ => hf i k) hi

theorem le_double_sum_nat {r : Finset ℕ} (f : ℕ → ℕ → ℕ) {i k : ℕ}
    (hi : i ∈ r) (hk : k ∈ r) : f i k ≤ ∑ i ∈ r, ∑ k ∈ r, f i k :=
  calc f i k ≤ ∑ k' ∈ r, f i k' := Finset.single_le_sum (fun k' _ => Nat.zero_le _) hk
    _ ≤ ∑ i ∈ r, ∑ k ∈ r, f i k :=
      Finset.single_le_sum (f := fun i => ∑ k ∈ r, f i k) (fun i _ => Nat.zero_le _) hi

theorem inv_one_add_le {κ S : ℝ} (hκ : 0 < κ) (hS : 1 / κ ≤ S) : 1 / (1 + S) ≤ κ := by
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  rw [div_le_iff₀ (by linarith)]
  rw [div_le_iff₀ hκ] at hS
  nlinarith

theorem inv_one_add_pos {S : ℝ} (hS : 0 ≤ S) : 0 < 1 / (1 + S) := by
  apply one_div_pos.2; linarith

theorem profileJetBound_of (hD : ProfileDict) (hJ : SliceJetBound) : ProfileJetBound := by
  intro F hF a b k x hx
  rw [hD F hF a b k x hx]
  exact hJ F hF a b k x.1 x.2.1 x.2.2 hx

theorem contDiffOn_trainProfile_of {F : ℝ → ℝ × ℝ → ℝ}
    (h : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => F x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ ∞ (trainProfile F) {y : ProfilePoint | 0 < y.2.2} := by
  have hg : ContDiff ℝ ∞ (fun y : ProfilePoint => (y.2.2, (y.1, y.2.1))) :=
    (contDiff_snd.comp contDiff_snd).prodMk (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  exact h.comp hg.contDiffOn (fun y hy => ⟨hy, mem_univ _⟩)

/-- Profile form of a function of `(s, η)` alone (the mean stream, mean remainder, mean stress). -/
theorem contDiffOn_trainProfile_of_eta {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ ∞ (trainProfile fun s z => G s z.2) {y : ProfilePoint | 0 < y.2.2} := by
  have hg : ContDiff ℝ ∞ (fun y : ProfilePoint => (y.2.2, y.2.1)) :=
    (contDiff_snd.comp contDiff_snd).prodMk (contDiff_fst.comp contDiff_snd)
  exact h.comp hg.contDiffOn (fun y hy => ⟨hy, mem_univ _⟩)

/-- **Finite uniformization** (no hypothesis on the train): a finite family of bounds
`T p j ≤ polyConst C_p N_p ν c · D κ_p` (each valid for `ν ≤ ν₀_p`) gives one bound for the sum
`∑_p |w p| T p j`, with `C = ∑ |w_p| max C_p 0`, `N = ∑ N_p`, `κ = (1+∑ 1/κ_p)⁻¹`,
`ν₀ = (1+∑ 1/ν₀_p)⁻¹`. -/
theorem finite_uniform {ι α : Type*} (S : Finset α) (Adm : ι → Prop) (ν c : ι → ℝ)
    (D : ℝ → ι → ℝ)
    (hD0 : ∀ κ j, Adm j → 0 ≤ D κ j)
    (hDm : ∀ κ κ' j, Adm j → 0 < κ' → κ' ≤ κ → D κ j ≤ D κ' j)
    (hpos : ∀ j, Adm j → 0 < ν j ∧ 0 < c j)
    (w : α → ℝ) (T : α → ι → ℝ)
    (hterm : ∀ p ∈ S, ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
      ∀ j, Adm j → ν j ≤ ν₀ → T p j ≤ polyConst C N (ν j) (c j) * D κ j) :
    ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧ ∀ j, Adm j → ν j ≤ ν₀ →
      ∑ p ∈ S, |w p| * T p j ≤ polyConst C N (ν j) (c j) * D κ j := by
  choose! Cf Nf κf νf hκf hνf hbd using hterm
  have hSκ : 0 ≤ ∑ p ∈ S, 1 / κf p :=
    Finset.sum_nonneg fun p hp => (one_div_pos.2 (hκf p hp)).le
  have hSν : 0 ≤ ∑ p ∈ S, 1 / νf p :=
    Finset.sum_nonneg fun p hp => (one_div_pos.2 (hνf p hp)).le
  refine ⟨∑ p ∈ S, |w p| * max (Cf p) 0, ∑ p ∈ S, Nf p, 1 / (1 + ∑ p ∈ S, 1 / κf p),
    1 / (1 + ∑ p ∈ S, 1 / νf p), inv_one_add_pos hSκ, inv_one_add_pos hSν, ?_⟩
  intro j hj hνj
  obtain ⟨hν, hc⟩ := hpos j hj
  set κ' := 1 / (1 + ∑ p ∈ S, 1 / κf p) with hκ'
  have hκ'pos : 0 < κ' := inv_one_add_pos hSκ
  set X := 1 + c j + (ν j)⁻¹ with hX
  have hX1 : 1 ≤ X := by
    have : 0 < (ν j)⁻¹ := inv_pos.2 hν
    linarith
  have hone : ∀ p ∈ S, T p j ≤ max (Cf p) 0 * X ^ (∑ p ∈ S, Nf p) * D κ' j := by
    intro p hp
    have hν_le : ν j ≤ νf p := by
      refine hνj.trans ?_
      have h1 : 1 / νf p ≤ ∑ p ∈ S, 1 / νf p :=
        Finset.single_le_sum (f := fun p => 1 / νf p)
          (fun p hp => (one_div_pos.2 (hνf p hp)).le) hp
      exact inv_one_add_le (hνf p hp) h1
    have hκ_le : κ' ≤ κf p := by
      have h1 : 1 / κf p ≤ ∑ p ∈ S, 1 / κf p :=
        Finset.single_le_sum (f := fun p => 1 / κf p)
          (fun p hp => (one_div_pos.2 (hκf p hp)).le) hp
      exact inv_one_add_le (hκf p hp) h1
    have h1 := hbd p hp j hj hν_le
    have hD := hDm (κf p) κ' j hj hκ'pos hκ_le
    have hpoly : polyConst (Cf p) (Nf p) (ν j) (c j) ≤ max (Cf p) 0 * X ^ (∑ p ∈ S, Nf p) := by
      unfold polyConst
      have hp1 : X ^ Nf p ≤ X ^ (∑ p ∈ S, Nf p) :=
        pow_le_pow_right₀ hX1
          (Finset.single_le_sum (f := Nf) (fun _ _ => Nat.zero_le _) hp)
      calc Cf p * X ^ Nf p ≤ max (Cf p) 0 * X ^ Nf p :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max (Cf p) 0 * X ^ (∑ p ∈ S, Nf p) :=
            mul_le_mul_of_nonneg_left hp1 (le_max_right _ _)
    calc T p j ≤ polyConst (Cf p) (Nf p) (ν j) (c j) * D (κf p) j := h1
      _ ≤ (max (Cf p) 0 * X ^ (∑ p ∈ S, Nf p)) * D (κf p) j :=
          mul_le_mul_of_nonneg_right hpoly (hD0 _ j hj)
      _ ≤ max (Cf p) 0 * X ^ (∑ p ∈ S, Nf p) * D κ' j :=
          mul_le_mul_of_nonneg_left hD (by positivity)
  calc ∑ p ∈ S, |w p| * T p j
      ≤ ∑ p ∈ S, |w p| * (max (Cf p) 0 * X ^ (∑ p ∈ S, Nf p) * D κ' j) :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hone p hp) (abs_nonneg _)
    _ = polyConst (∑ p ∈ S, |w p| * max (Cf p) 0) (∑ p ∈ S, Nf p) (ν j) (c j) * D κ' j := by
        unfold polyConst
        rw [← hX, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

/-- **Generic finite assembly** (no hypothesis on the train).  Let `G j` be profile functions,
`C^∞` for `s > 0`, indexed by admissible instances `j` (carrying `ν j, c j > 0`, a point `x j`
with `s ≥ 1`).  If for every pair `(i, k)` the term
`(1+η²/s)^m |η|^i s^k |∂_η^{i+a} ∂_q^b ∂_s^k G|` is bounded by `polyConst C N ν c · D κ`
(`C, N, κ, ν₀` depending on `(i, k)`, `D` antitone in `κ` and nonnegative), then so is
`(1+η²/s)^m |K^ℓ ∂_η^a ∂_q^b G|`, with one common `(C, N, κ, ν₀)`.  Used for the exponential
decay `D κ j = exp(-κνs/c²)` and for the power decay `D κ j = s^{-β}`. -/
theorem late_assembly {ι : Type*} (hK : KExpansion) (hC : ProfileIterComm)
    (Adm : ι → Prop) (ν c : ι → ℝ) (x : ι → ProfilePoint) (G : ι → ProfilePoint → ℝ)
    (D : ℝ → ι → ℝ)
    (hD0 : ∀ κ j, Adm j → 0 ≤ D κ j)
    (hDm : ∀ κ κ' j, Adm j → 0 < κ' → κ' ≤ κ → D κ j ≤ D κ' j)
    (hpos : ∀ j, Adm j → 0 < ν j ∧ 0 < c j ∧ 1 ≤ (x j).2.2)
    (hsm : ∀ j, Adm j → ContDiffOn ℝ ∞ (G j) {y : ProfilePoint | 0 < y.2.2})
    (ℓ a b m : ℕ)
    (hterm : ∀ i k : ℕ, ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
      ∀ j, Adm j → ν j ≤ ν₀ →
        (1 + (x j).2.1 ^ 2 / (x j).2.2) ^ m * (|(x j).2.1| ^ i * (x j).2.2 ^ k *
          |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (G j)))) (x j)|) ≤
          polyConst C N (ν j) (c j) * D κ j) :
    ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧ ∀ j, Adm j → ν j ≤ ν₀ →
      (1 + (x j).2.1 ^ 2 / (x j).2.2) ^ m *
        |(ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (G j)))) (x j)| ≤
        polyConst C N (ν j) (c j) * D κ j := by
  obtain ⟨n, hn⟩ := hK ℓ
  choose Cf Nf κf νf hκf hνf hbd using hterm
  set r := Finset.range (ℓ + 1) with hr
  have hSκ : 0 ≤ ∑ i ∈ r, ∑ k ∈ r, 1 / κf i k :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => (one_div_pos.2 (hκf i k)).le
  have hSν : 0 ≤ ∑ i ∈ r, ∑ k ∈ r, 1 / νf i k :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => (one_div_pos.2 (hνf i k)).le
  refine ⟨∑ i ∈ r, ∑ k ∈ r, |n i k| * max (Cf i k) 0, ∑ i ∈ r, ∑ k ∈ r, Nf i k,
    1 / (1 + ∑ i ∈ r, ∑ k ∈ r, 1 / κf i k), 1 / (1 + ∑ i ∈ r, ∑ k ∈ r, 1 / νf i k),
    inv_one_add_pos hSκ, inv_one_add_pos hSν, ?_⟩
  intro j hj hνj
  obtain ⟨hν, hc, hs1⟩ := hpos j hj
  have hs0 : 0 < (x j).2.2 := by linarith
  have hGs := hsm j hj
  have hH : ContDiffOn ℝ ∞ (partialEta^[a] (partialQ^[b] (G j)))
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter (contDiffOn_partialQ_iter hGs b) a
  have hexp := hn _ hH (x j) hs0
  have hterm_eq : ∀ i k : ℕ,
      (partialEta^[i] (partialAge^[k] (partialEta^[a] (partialQ^[b] (G j))))) (x j) =
        (partialEta^[i + a] (partialQ^[b] (partialAge^[k] (G j)))) (x j) :=
    fun i k => hC (G j) hGs i a b k (x j) hs0
  simp_rw [hterm_eq] at hexp
  set κ' := 1 / (1 + ∑ i ∈ r, ∑ k ∈ r, 1 / κf i k) with hκ'
  set ν' := 1 / (1 + ∑ i ∈ r, ∑ k ∈ r, 1 / νf i k) with hν'
  have hκ'pos : 0 < κ' := inv_one_add_pos hSκ
  set X := 1 + c j + (ν j)⁻¹ with hX
  have hX1 : 1 ≤ X := by
    have : 0 < (ν j)⁻¹ := inv_pos.2 hν
    linarith
  set W := (1 + (x j).2.1 ^ 2 / (x j).2.2) ^ m with hW
  have hW0 : 0 ≤ W := by positivity
  have hN : ∀ i ∈ r, ∀ k ∈ r, Nf i k ≤ ∑ i ∈ r, ∑ k ∈ r, Nf i k :=
    fun i hi k hk => le_double_sum_nat Nf hi hk
  -- the bound for one term
  have hone : ∀ i ∈ r, ∀ k ∈ r,
      W * (|(x j).2.1| ^ i * (x j).2.2 ^ k *
        |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (G j)))) (x j)|) ≤
      max (Cf i k) 0 * X ^ (∑ i ∈ r, ∑ k ∈ r, Nf i k) * D κ' j := by
    intro i hi k hk
    have hν_le : ν j ≤ νf i k := by
      refine hνj.trans ?_
      have h1 : 1 / νf i k ≤ ∑ i ∈ r, ∑ k ∈ r, 1 / νf i k :=
        le_double_sum_real (fun i k => (one_div_pos.2 (hνf i k)).le) hi hk
      exact inv_one_add_le (hνf i k) h1
    have hκ_le : κ' ≤ κf i k := by
      have h1 : 1 / κf i k ≤ ∑ i ∈ r, ∑ k ∈ r, 1 / κf i k :=
        le_double_sum_real (fun i k => (one_div_pos.2 (hκf i k)).le) hi hk
      exact inv_one_add_le (hκf i k) h1
    have h1 := hbd i k j hj hν_le
    have hD := hDm (κf i k) κ' j hj hκ'pos hκ_le
    have hD0' := hD0 κ' j hj
    have hpoly : polyConst (Cf i k) (Nf i k) (ν j) (c j) ≤
        max (Cf i k) 0 * X ^ (∑ i ∈ r, ∑ k ∈ r, Nf i k) := by
      unfold polyConst
      have hp1 : X ^ Nf i k ≤ X ^ (∑ i ∈ r, ∑ k ∈ r, Nf i k) :=
        pow_le_pow_right₀ hX1 (hN i hi k hk)
      calc Cf i k * X ^ Nf i k ≤ max (Cf i k) 0 * X ^ Nf i k :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max (Cf i k) 0 * X ^ (∑ i ∈ r, ∑ k ∈ r, Nf i k) :=
            mul_le_mul_of_nonneg_left hp1 (le_max_right _ _)
    calc _ ≤ polyConst (Cf i k) (Nf i k) (ν j) (c j) * D (κf i k) j := h1
      _ ≤ (max (Cf i k) 0 * X ^ (∑ i ∈ r, ∑ k ∈ r, Nf i k)) * D (κf i k) j :=
          mul_le_mul_of_nonneg_right hpoly (hD0 _ j hj)
      _ ≤ max (Cf i k) 0 * X ^ (∑ i ∈ r, ∑ k ∈ r, Nf i k) * D κ' j :=
          mul_le_mul_of_nonneg_left hD (by positivity)
  rw [hexp]
  calc W * |∑ i ∈ r, ∑ k ∈ r, n i k * (x j).2.1 ^ i * (x j).2.2 ^ k *
        (partialEta^[i + a] (partialQ^[b] (partialAge^[k] (G j)))) (x j)|
      ≤ W * ∑ i ∈ r, ∑ k ∈ r, |n i k| * (|(x j).2.1| ^ i * (x j).2.2 ^ k *
        |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (G j)))) (x j)|) := by
        apply mul_le_mul_of_nonneg_left _ hW0
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos hs0]
        apply le_of_eq
        ring
    _ = ∑ i ∈ r, ∑ k ∈ r, |n i k| * (W * (|(x j).2.1| ^ i * (x j).2.2 ^ k *
        |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (G j)))) (x j)|)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ ∑ i ∈ r, ∑ k ∈ r, |n i k| * (max (Cf i k) 0 * X ^ (∑ i ∈ r, ∑ k ∈ r, Nf i k) *
        D κ' j) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (hone i hi k hk) (abs_nonneg _)
    _ = polyConst (∑ i ∈ r, ∑ k ∈ r, |n i k| * max (Cf i k) 0) (∑ i ∈ r, ∑ k ∈ r, Nf i k)
          (ν j) (c j) * D κ' j := by
        unfold polyConst
        rw [← hX, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring


/-! ### From `TrainFluctuationDecay` to a term bound -/

/-- A weighted sup-norm bound gives a pointwise bound. -/
theorem pointwise_of_wSupNorm {E : Type*} [NormedAddCommGroup E] {m : ℕ} {f : ℝ × ℝ → E}
    {B : ℝ} (hB : 0 ≤ B) (h : UnforcedLeray.Short.PartI.wSupNorm m f ≤ ENNReal.ofReal B)
    (z : ℝ × ℝ) : Real.sqrt (UnforcedLeray.Train.jap m z) * ‖f z‖ ≤ B := by
  have h1 : ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ ≤
      UnforcedLeray.Short.PartI.wSupNorm m f :=
    le_iSup (fun z : ℝ × ℝ => ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ) z
  have h2 := h1.trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hB] at h2
  exact h2

theorem sqrt_jap_even (m : ℕ) (z : ℝ × ℝ) :
    Real.sqrt (UnforcedLeray.Train.jap (2 * m) z) = (1 + z.2 ^ 2) ^ m := by
  unfold UnforcedLeray.Train.jap
  rw [pow_mul', Real.sqrt_sq (by positivity)]

theorem weight_le (m i : ℕ) {η s : ℝ} (hs : 1 ≤ s) :
    (1 + η ^ 2 / s) ^ m * |η| ^ i ≤ (1 + η ^ 2) ^ (m + i) := by
  have hs0 : 0 < s := by linarith
  have h1 : 1 + η ^ 2 / s ≤ 1 + η ^ 2 := by
    have : η ^ 2 / s ≤ η ^ 2 := div_le_self (sq_nonneg _) hs
    linarith
  have h2 : |η| ≤ 1 + η ^ 2 := by
    nlinarith [sq_nonneg (|η| - 1), sq_abs η]
  have h3 : (1 + η ^ 2 / s) ^ m ≤ (1 + η ^ 2) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  have h4 : |η| ^ i ≤ (1 + η ^ 2) ^ i := pow_le_pow_left₀ (abs_nonneg _) h2 i
  rw [pow_add]
  exact mul_le_mul h3 h4 (by positivity) (by positivity)

/-- **Core term bound** (steps (ii)-(iii) of the route): a weighted sup-norm bound for the
`(k, i+a+b)`-jet of `F` with weight exponent `2(m+i)` bounds the profile term, at ages `s ≥ 1`. -/
theorem jet_term_core {F : ℝ → ℝ × ℝ → ℝ} (hJ : ProfileJetBound)
    (hFs : ContDiffOn ℝ ∞ (trainProfile F) {y : ProfilePoint | 0 < y.2.2})
    (m a b i k : ℕ) {x : ProfilePoint} (hx : 1 ≤ x.2.2) {B : ℝ} (hB : 0 ≤ B)
    (hw : UnforcedLeray.Short.PartI.wSupNorm (2 * (m + i)) (ageJet k (i + a + b) F x.2.2) ≤
      ENNReal.ofReal B) :
    (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
      |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (trainProfile F)))) x|) ≤
      x.2.2 ^ k * B := by
  have hs0 : 0 < x.2.2 := by linarith
  have h1 := hJ F hFs (i + a) b k x hs0
  have h2 := pointwise_of_wSupNorm hB hw (x.1, x.2.1)
  rw [sqrt_jap_even] at h2
  have hwt := weight_le m i (η := x.2.1) hx
  have hsk : 0 ≤ x.2.2 ^ k := by positivity
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
        |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (trainProfile F)))) x|)
      = ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |x.2.1| ^ i) * x.2.2 ^ k *
        |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (trainProfile F)))) x| := by ring
    _ ≤ (1 + x.2.1 ^ 2) ^ (m + i) * x.2.2 ^ k *
        ‖ageJet k (i + a + b) F x.2.2 (x.1, x.2.1)‖ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hwt hsk) h1 (abs_nonneg _) (by positivity)
    _ = x.2.2 ^ k * ((1 + x.2.1 ^ 2) ^ (m + i) *
        ‖ageJet k (i + a + b) F x.2.2 (x.1, x.2.1)‖) := by ring
    _ ≤ x.2.2 ^ k * B := mul_le_mul_of_nonneg_left h2 hsk

/-- The term bounds for the stream fluctuation `ψ̃` and the pressure `p` (all `(i, k)`). -/
def FluctTermBound : Prop :=
  ∀ (ρ : ℝ) (m a b i k : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        ((1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
          |(partialEta^[i + a] (partialQ^[b] (partialAge^[k]
            (trainProfile fun s z => tr.ψ s z - meanStream tr s z.2)))) x|) ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) ∧
        ((1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
          |(partialEta^[i + a] (partialQ^[b] (partialAge^[k] (trainProfile tr.p)))) x|) ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)))

theorem fluctTermBound_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hJ : ProfileJetBound) (hA : ExpPowAbsorb) (hFS : FluctProfileSmooth)
    (hS : LateProfileSmooth) : FluctTermBound := by
  intro ρ m a b i k hρ
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, H⟩ := hF ρ hρ (2 * (m + i)) k (i + a + b)
  obtain ⟨C₂, N₂, hC₂, hAb⟩ := hA κ k hκ
  refine ⟨C * C₂, N + N₂, κ / 2, ν₀, by positivity, hν₀, ?_⟩
  intro ν hν hνν₀ tr hb x hx
  have hs0 : 0 < x.2.2 := by linarith
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have Hs := H ν hν hνν₀ tr hb x.2.2 hs0
  obtain ⟨⟨_, hψ⟩, _, ⟨_, hp⟩⟩ := Hs
  have hB : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
      Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := by
    unfold UnforcedLeray.Short.PartI.polyP
    have : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
      have : 0 < ν⁻¹ := inv_pos.2 hν
      linarith
    positivity
  have habs := hAb ν (ν ^ (-ρ)) x.2.2 hν hc hs0.le
  have hfin : ∀ {T : ℝ}, T ≤ x.2.2 ^ k * (UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
      Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) →
      T ≤ polyConst (C * C₂) (N + N₂) ν (ν ^ (-ρ)) *
        Real.exp (-(κ / 2 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := by
    intro T hT
    refine hT.trans ?_
    have hP : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) := by
      unfold UnforcedLeray.Short.PartI.polyP
      have : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
        have : 0 < ν⁻¹ := inv_pos.2 hν
        linarith
      positivity
    calc x.2.2 ^ k * (UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
          Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)))
        = UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
          (x.2.2 ^ k * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) := by ring
      _ ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
          (polyConst C₂ N₂ ν (ν ^ (-ρ)) * Real.exp (-(κ / 2 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) :=
          mul_le_mul_of_nonneg_left habs hP
      _ = polyConst (C * C₂) (N + N₂) ν (ν ^ (-ρ)) *
          Real.exp (-(κ / 2 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := by
          unfold UnforcedLeray.Short.PartI.polyP polyConst
          rw [pow_add]
          ring
  exact ⟨hfin (jet_term_core hJ (hFS ν (ν ^ (-ρ)) hν hc tr hb) m a b i k hx hB hψ),
    hfin (jet_term_core hJ (hS ν (ν ^ (-ρ)) hν hc tr hb).2 m a b i k hx hB hp)⟩

/-- **`PartII-a:R02/2`, conditional** (`LateFluctuationProfile`): the fluctuation profile bounds
follow from `TrainFluctuationDecay`, the smoothness of the profiles, and the calculus leaves
`KExpansion`, `ProfileIterComm`, `ProfileDict`, `SliceJetBound`, `ExpPowAbsorb`. -/
theorem lateFluctuationProfile_of_sub (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hS : LateProfileSmooth) (hFS : FluctProfileSmooth) (hK : KExpansion)
    (hC : ProfileIterComm) (hD : ProfileDict) (hJ : SliceJetBound) (hA : ExpPowAbsorb) :
    LateFluctuationProfile := by
  intro ρ m a b ℓ hρ
  have hT := fluctTermBound_of hF (profileJetBound_of hD hJ) hA hFS hS
  let ι : Type := Σ ν : ℝ, {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)) // UnforcedLeray.Short.PartI.IsBUCTrain tr} × ProfilePoint × Bool
  have key := late_assembly (ι := ι) hK hC
    (fun j => 0 < j.1 ∧ 1 ≤ j.2.2.1.2.2) (fun j => j.1) (fun j => j.1 ^ (-ρ))
    (fun j => j.2.2.1)
    (fun j => cond j.2.2.2
      (trainProfile fun s z => j.2.1.1.ψ s z - meanStream j.2.1.1 s z.2) (trainProfile j.2.1.1.p))
    (fun κ j => Real.exp (-(κ * j.1 * j.2.2.1.2.2 / (j.1 ^ (-ρ)) ^ 2)))
    (fun κ j _ => (Real.exp_pos _).le)
    (by
      intro κ κ' j hj hκ' hκκ'
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have : 0 ≤ j.1 * j.2.2.1.2.2 := mul_nonneg hj.1.le (by linarith [hj.2])
      nlinarith)
    (fun j hj => ⟨hj.1, Real.rpow_pos_of_pos hj.1 _, hj.2⟩)
    (by
      rintro ⟨ν, ⟨tr, hb⟩, x, β⟩ ⟨hν, _⟩
      have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
      cases β
      · exact (hS ν (ν ^ (-ρ)) hν hc tr hb).2
      · exact hFS ν (ν ^ (-ρ)) hν hc tr hb)
    ℓ a b m
    (by
      intro i k
      obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := hT ρ m a b i k hρ
      refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
      rintro ⟨ν, ⟨tr, hb⟩, x, β⟩ ⟨hν, hx⟩ hνν₀
      cases β
      · exact (H ν hν hνν₀ tr hb x hx).2
      · exact (H ν hν hνν₀ tr hb x hx).1)
  obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := key
  refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
  intro ν hν hνν₀ tr hb x hx
  exact ⟨H ⟨ν, ⟨tr, hb⟩, x, true⟩ ⟨hν, hx⟩ hνν₀, H ⟨ν, ⟨tr, hb⟩, x, false⟩ ⟨hν, hx⟩ hνν₀⟩

end UnforcedLeray.Short.PartIIa
