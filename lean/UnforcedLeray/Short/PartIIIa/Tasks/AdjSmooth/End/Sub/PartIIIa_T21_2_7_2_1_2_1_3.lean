import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/2/1/3`: `TimeJetPartialBdd` from five leaves

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3061
(the weighted energies `E_j` of the reverse-time adjoint, `H^j_{-m}` norms, continuity in the age
up to the end age) with the Sobolev-type sup bound for the periodic cell.

The three analytic steps (i), (ii), (iii) of `TimeJetPartialBdd` are the leaves
`TimeIterDerivAe`/`SmoothAeJet` (i), `SupBddByXNorm` (ii), `TimeJetXNormBdd` (iii), plus the
calculus leaf `StPartialSmooth` (the slices of the classical partials are smooth).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf (calculus)**: a field jointly `C^∞` on the open set `(t, s) × ℝ²` has all classical
partials `∂^w ∂_r^j φ'(r, ·)` smooth in `x` at every `r ∈ (t, s)` (the age derivatives of a jointly
smooth function are jointly smooth, then restrict to the slice). -/
def StPartialSmooth : Prop :=
  ∀ (φ' : ℝ → ℝ × ℝ → ℂ) (t s : ℝ),
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ) →
    ∀ (j : ℕ) (w : List (Fin 2)), ∀ r ∈ Ioo t s, ContDiff ℝ ∞ (stPartial φ' j w r)

/-- **Leaf (i), age derivatives** (SP 3060-3061): if `Φ` are time jets on `[t, s)` and `φ'` is a
version of `Φ 0` jointly `C^∞` on `(t, s) × ℝ²`, then for `r ∈ (t, s)` the classical age derivative
`∂_r^j φ'(r, ·)` equals `Φ j r` almost everywhere. Induction on `j`: the classical difference
quotients converge pointwise; those of `Φ j` converge to `Φ (j+1) r` in `X_{-m,c}` (`hΦ.2`), hence
almost everywhere on the cell along a sequence (`tendstoInMeasure_of_tendsto_eLpNorm`,
`TendstoInMeasure.exists_seq_tendsto_ae`); both sides are `c`-periodic up to null sets, and
a smooth function that is almost everywhere periodic is periodic (`adjPeriodic_of_ae_eq`,
`periodicAeOfCell`). -/
def TimeIterDerivAe : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ) (φ' : ℝ → ℝ × ℝ → ℂ), 0 < c → t < s →
    IsAdjTimeJets c m (Ico t s) Φ → (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] Φ 0 r) →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ) →
    ∀ j : ℕ, ∀ r ∈ Ioo t s, stPartial φ' j [] r =ᵐ[volume] Φ j r

/-- **Leaf (i), spatial derivatives**: a smooth function `h` equal almost everywhere to a field `f`
with `c`-periodic weak derivative fields `D` up to order `K` (`IsCellJet`) is `c`-periodic, and
its classical spatial partials `adjSpatial w h`, `|w| ≤ K`, are `c`-periodic and equal to `D w`
almost everywhere on the plane. (Classical derivatives of a smooth `c`-periodic function are weak
cell derivatives: integrate by parts in `x₁` over one period and in `x₂` inside the band of the
test; weak cell derivatives are unique almost everywhere on the cell, fundamental lemma for the
cylinder tests; `HasWeakCellDerivC.congr_ae`; then `periodicAeOfCell`.) -/
def SmoothAeJet : Prop :=
  ∀ (c m : ℝ) (K : ℕ) (h f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ), 0 < c →
    ContDiff ℝ ∞ h → IsCellJet c m K f D → h =ᵐ[volume] f →
    ∀ w : List (Fin 2), w.length ≤ K →
      (∀ x : ℝ × ℝ, adjSpatial w h (x.1 + c, x.2) = adjSpatial w h x) ∧
        adjSpatial w h =ᵐ[volume] D w

/-- The words of length at most `2` over `Fin 2`. -/
def wordsLe2 : List (List (Fin 2)) := [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]]

/-- **Leaf (ii), sup bound by weighted norms** (SP 3060-3061): for a smooth `c`-periodic `g` and
`‖x‖ ≤ R`, `|g x| ≤ C(c, m, R) Σ_{|w| ≤ 2} ‖∂^w g‖_{X_{-m,c}}` (cutoff `ζ ∈ C_c^∞` equal to `1` on
the ball, `g = ∫∫ ∂₁∂₂(ζg)` over a quadrant, Cauchy-Schwarz, the support meets finitely many
periods, `B0579.jb ^ (-m)` is bounded below on bounded sets). In `ℝ≥0∞`, so no finiteness
hypothesis is needed. -/
def SupBddByXNorm : Prop :=
  ∀ (c m R : ℝ), 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g →
    (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) → ∀ x : ℝ × ℝ, ‖x‖ ≤ R →
      ENNReal.ofReal ‖g x‖ ≤
        ENNReal.ofReal C * (wordsLe2.map fun w => xNorm c (-m) (adjSpatial w g)).sum

/-- **Leaf (iii), the weighted norms stay bounded up to the end age** (SP 3060-3061, `AdjHkOn`):
for time jets on `[t, s)`, every order `k` and `n`, there is a bound `C` such that for each
`j ≤ n` the derivative fields `D` of `Φ j` (cell jets of order `k` on `[t, s)`) satisfy
`‖D r w‖_{X_{-m,c}} ≤ C` for `|w| ≤ k` and `r ∈ (t, t + (s - t)/2)`. (`r ↦ ‖D r w‖` is continuous
on `[t, s)` by the `Tendsto` of `AdjHkOn` and the `eLpNorm` triangle inequality, finite by `memX`,
so bounded on the compact `[t, t + (s - t)/2] ⊆ [t, s)`; finitely many `(j, w)`.) -/
def TimeJetXNormBdd : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ), t < s → IsAdjTimeJets c m (Ico t s) Φ →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ j ≤ n, ∃ D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ,
      (∀ r ∈ Ico t s, IsCellJet c m k (Φ j r) (D r)) ∧
        ∀ w : List (Fin 2), w.length ≤ k → ∀ r ∈ Ioo t (t + (s - t) / 2),
          xNorm c (-m) (D r w) ≤ ENNReal.ofReal C

theorem adjSpatial_append (w' w : List (Fin 2)) (Ψ : ℝ × ℝ → ℂ) :
    adjSpatial w' (adjSpatial w Ψ) = adjSpatial (w' ++ w) Ψ := by
  induction w' with
  | nil => rfl
  | cons k w' ih => simp only [List.cons_append, adjSpatial, ih]

theorem timeJetPartialBdd_of (h1 : StPartialSmooth) (h2 : TimeIterDerivAe) (h3 : SmoothAeJet)
    (h4 : SupBddByXNorm) (h5 : TimeJetXNormBdd) : TimeJetPartialBdd := by
  intro c m t s Φ φ' hc hts hΦ hae hsm n R
  obtain ⟨C0, hC0⟩ := h5 c m t s Φ hts hΦ (n + 2) n
  obtain ⟨C1, hC1n, hC1⟩ := h4 c m R hc
  choose D hD hDb using hC0
  refine ⟨(s - t) / 2, by linarith, C1 * (7 * max C0 0), fun j hj w hw r hr x hx => ?_⟩
  have hrI : r ∈ Ioo t s := ⟨hr.1, by linarith [hr.2]⟩
  have hrC : r ∈ Ico t s := ⟨hr.1.le, hrI.2⟩
  set h : ℝ × ℝ → ℂ := stPartial φ' j [] r with hh
  have hhs : ContDiff ℝ ∞ h := h1 φ' t s hsm j [] r hrI
  have hae0 : h =ᵐ[volume] Φ j r := h2 c m t s Φ φ' hc hts hΦ hae hsm j r hrI
  have hJ := h3 c m (n + 2) h (Φ j r) (D j hj r) hc hhs (hD j hj r hrC) hae0
  have hg : ∀ w'' : List (Fin 2), stPartial φ' j w'' r = adjSpatial w'' h := fun w'' => rfl
  have hper := (hJ w (by omega)).1
  have hgs : ContDiff ℝ ∞ (adjSpatial w h) := by rw [← hg]; exact h1 φ' t s hsm j w r hrI
  have hxn : ∀ w' ∈ wordsLe2, xNorm c (-m) (adjSpatial w' (adjSpatial w h)) ≤
      ENNReal.ofReal C0 := by
    intro w' hw'
    have hl : w'.length ≤ 2 := by simp [wordsLe2] at hw'; rcases hw' with h | h | h | h | h | h | h <;> simp [h]
    rw [adjSpatial_append]
    have hae1 := (hJ (w' ++ w) (by rw [List.length_append]; omega)).2
    have hac : B0579.cellMeasure c (-m) ≪ volume :=
      (B0579.cellMeasure_ac c (-m)).trans Measure.restrict_le_self.absolutelyContinuous
    calc xNorm c (-m) (adjSpatial (w' ++ w) h) = xNorm c (-m) (D j hj r (w' ++ w)) :=
          eLpNorm_congr_ae (hac.ae_eq hae1)
      _ ≤ _ := hDb j hj (w' ++ w) (by rw [List.length_append]; omega) r hr
  have hsum : (wordsLe2.map fun w' => xNorm c (-m) (adjSpatial w' (adjSpatial w h))).sum ≤
      7 * ENNReal.ofReal C0 := by
    have := List.sum_le_card_nsmul (wordsLe2.map fun w' => xNorm c (-m) (adjSpatial w' (adjSpatial w h)))
      (ENNReal.ofReal C0) (by
        intro a ha
        obtain ⟨w', hw', rfl⟩ := List.mem_map.1 ha
        exact hxn w' hw')
    simpa [wordsLe2, nsmul_eq_mul] using this
  have key := hC1 (adjSpatial w h) hgs hper x hx
  have hfin : ENNReal.ofReal ‖adjSpatial w h x‖ ≤ ENNReal.ofReal (C1 * (7 * max C0 0)) := by
    calc ENNReal.ofReal ‖adjSpatial w h x‖
        ≤ ENNReal.ofReal C1 * (wordsLe2.map fun w' =>
            xNorm c (-m) (adjSpatial w' (adjSpatial w h))).sum := key
      _ ≤ ENNReal.ofReal C1 * (7 * ENNReal.ofReal C0) := by gcongr
      _ = ENNReal.ofReal (C1 * (7 * max C0 0)) := by
          rw [ENNReal.ofReal_mul hC1n, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7)]
          have : ENNReal.ofReal (max C0 0) = ENNReal.ofReal C0 := by
            unfold ENNReal.ofReal
            congr 1
            ext
            simp [Real.coe_toNNReal']
          rw [this]; simp
  have hnn : 0 ≤ C1 * (7 * max C0 0) := by positivity
  rw [hg]
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 hfin

end UnforcedLeray.Short.IIIa
