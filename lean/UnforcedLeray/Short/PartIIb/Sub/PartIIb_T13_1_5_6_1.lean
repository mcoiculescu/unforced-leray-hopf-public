import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6

/-!
# Decomposition of `CgiLimitCauchy` (task `PartII-b:T13/1/5/6/1`)

Source `the November 2 reference manuscript`
1932-1933: apply the a priori inequality (`AprioriAt`, `λ = 1`) to `w n - w m`; the first derivatives
`∂_i w n` are Cauchy in `L^r(cylMeas c)`; completeness gives the limit.

* `CgiDerivPer`: derivatives of a nice function are `q`-periodic everywhere.
* `CgiCauchyDiff`: the Cauchy property of `∂_i w n` (needs measurability of `u` and `D2`).
* `CgiPerLimit`: completeness of `L^r(cylMeas c)` plus the periodic measurable modification of the
  limit of a Cauchy sequence of continuous, everywhere `q`-periodic functions.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- **Leaf A.** For a nice `w`, `∂_i w` (`i = 1, 2`, i.e. `q, η`) is `q`-periodic everywhere
(`w ∘ qShift c = w`, `qShift` a translation, so `fderiv` commutes). -/
def CgiDerivPer : Prop :=
  ∀ r c : ℝ, ∀ w : Coord → ℂ, CgiNice c r w → ∀ (i : Fin 2) (x : Coord),
    cdv i.succ w (qShift c x) = cdv i.succ w x

/-- **Leaf B (SP 1932).** `CgiNice` is closed under subtraction; `AprioriAt c r C` with `λ = 1`
applied to `w n - w m` gives `‖∂_i(w n - w m)‖ ≤ C(‖w n - w m‖ + Σ‖∂_k∂_l(w n - w m)‖)`; the right
side is `≤ C(‖w n - u‖ + ‖w m - u‖ + Σ(‖∂²w n - D2‖ + ‖∂²w m - D2‖))` by the triangle inequality
(`u`, `D2` measurable, so `eLpNorm_add_le` applies), which tends to `0` by `CgiApprox`. -/
def CgiCauchyDiff : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c C : ℝ, 0 < c → 0 < C → AprioriAt c r C →
    ∀ (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) (w : ℕ → Coord → ℂ),
    CgiApprox c r u D2 w → AEStronglyMeasurable u volume →
    (∀ k l : Fin 2, AEStronglyMeasurable (D2 k l) volume) →
    ∀ i : Fin 2, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      cylNorm c r (fun x => cdv i.succ (w n) x - cdv i.succ (w m) x) < ε

/-- **Leaf C (completeness + periodic modification).** `L^r(cylMeas c)` is complete; the `Lp`
limit `G₀` of a Cauchy sequence of continuous functions with finite norm is replaced by
`G x := G₀ (x.1, (x.2.1 - c ⌊(x.2.1 + c/2)/c⌋, x.2.2))` (which equals `G₀` `cylMeas`-a.e. since
`cylMeas c` lives on the cell `q ∈ [-c/2, c/2)`, and the sequence is periodic), so that `G` is
`QPeriodicS` and `AEStronglyMeasurable volume`. -/
def CgiPerLimit : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c → ∀ g : ℕ → Coord → ℂ,
    (∀ n, Continuous (g n)) → (∀ n, cylNorm c r (g n) < ⊤) →
    (∀ n x, g n (qShift c x) = g n x) →
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      cylNorm c r (fun x => g n x - g m x) < ε) →
    ∃ G : Coord → ℂ, QPeriodicS c G ∧ AEStronglyMeasurable G volume ∧
      Tendsto (fun n => cylNorm c r (fun x => g n x - G x)) atTop (𝓝 0)

theorem cgiLimitCauchy_of (hA : CgiDerivPer) (hB : CgiCauchyDiff) (hC : CgiPerLimit) :
    CgiLimitCauchy := by
  intro r hr c C hc hC' hAp u D2 w hw hum hD2
  have hcont : ∀ (n : ℕ) (i : Fin 2), Continuous (cdv i.succ (w n)) := by
    intro n i
    unfold cdv
    exact ((hw.1 n).smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have key : ∀ i : Fin 2, ∃ G : Coord → ℂ, QPeriodicS c G ∧ AEStronglyMeasurable G volume ∧
      Tendsto (fun n => cylNorm c r (fun x => cdv i.succ (w n) x - G x)) atTop (𝓝 0) :=
    fun i => hC r hr c hc (fun n => cdv i.succ (w n)) (fun n => hcont n i)
      (fun n => (hw.1 n).mem1 i) (fun n x => hA r c (w n) (hw.1 n) i x)
      (hB r hr c C hc hC' hAp u D2 w hw hum hD2 i)
  choose G hG using key
  exact ⟨G, fun i => ⟨(hG i).1, (hG i).2.1⟩, fun i => (hG i).2.2⟩

end UnforcedLeray.Short.IIb
