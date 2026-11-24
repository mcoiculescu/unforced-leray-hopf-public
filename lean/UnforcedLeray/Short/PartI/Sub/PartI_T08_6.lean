import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ViscousIBP

/-!


Source: `the November 2 reference manuscript`,
line 346 (the pressure term of the differentiated energy; `div e = 0`).

`jetPressureOrth_proof` follows from
* `JetPressureOrthWord`: for a nonempty word `w`, `∑_k ∫ ∂_w f_k ∂_w ∂_k P = 0` (integrate `∂_k`
  by parts onto `∂_k ∂_w f_k`; the sum is `∂_w div f = 0`);
* `JetPressureOrthZero`: the order-zero case `∫ f · ∇P = 0` (boundary terms at `η = ±R` vanish).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Order `≥ 1` (source line 346). With `w = β :: w'`: `∂_w ∂_k P = ∂_k ∂_w P` (commuting
partials), `∂_w P = derivWord w' (∂_β P) ∈ L²`; integrate `∂_k` by parts with
`Cyl.integral_cell_partialQ_mul` (periodic) and `Cyl.integral_cell_partialEta_mul` to get
`-∫ ∂_w(div f) ∂_w P = 0`. -/
def JetPressureOrthWord : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Plane → Train.Vec, CellSmoothL2 c f → (∀ z : Plane, Cyl.divergence f z = 0) →
    ∀ P : Plane → ℝ, ContDiff ℝ ∞ P → Cyl.IsPeriodic c P →
    (∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (Train.gradS P) k) 2 (Cyl.cellμ c)) →
    ∀ w : List Bool, w ≠ [] →
      ∑ k : Fin 2, ∫ z in Cyl.cell c, wordComp w f k z * wordComp w (Train.gradS P) k z = 0

/-- Order `0` (source line 346). `f · ∇P = div (P f)` is in `L¹`; on the slab `|η| ≤ R` the
`q`-part vanishes by periodicity and the `η`-part is `∫_q (P f₂)(q,R) - (P f₂)(q,-R) dq`;
`φ(η) = ∫_q f₂(q,η)² dq` is integrable with integrable derivative `2∫_q f₂ ∂_η f₂`, so
`φ(±R) → 0`, and `|∫_q P f₂| ≤ M √c √φ`; dominated convergence for the slab integrals. -/
def JetPressureOrthZero : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Plane → Train.Vec, CellSmoothL2 c f → (∀ z : Plane, Cyl.divergence f z = 0) →
    ∀ P : Plane → ℝ, ContDiff ℝ ∞ P → Cyl.IsPeriodic c P → (∃ M : ℝ, ∀ z : Plane, |P z| ≤ M) →
    (∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (Train.gradS P) k) 2 (Cyl.cellμ c)) →
    jetPair c 0 f (Train.gradS P) = 0

theorem jetPressureOrth_of (h1 : JetPressureOrthWord) (h0 : JetPressureOrthZero) :
    JetPressureOrth := by
  intro c hc f hf hdiv P hP hper hM hL2P j
  cases j with
  | zero => exact h0 c hc f hf hdiv P hP hper hM hL2P
  | succ j =>
    obtain ⟨hs, hp, hL2⟩ := hf
    have hI : ∀ (w : List Bool) (k : Fin 2),
        IntegrableOn (fun z => wordComp w f k z * wordComp w (Train.gradS P) k z) (Cyl.cell c) :=
      fun w k => (hL2 w k).integrable_mul (hL2P w k)
    unfold jetPair
    rw [JetViscIBP.integral_sum_sum _ _ (fun w _ k => hI w k)]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hlen : w.length = j + 1 := JetViscIBP.mem_wordsOfLength_iff'.1 hw
    have hne : w ≠ [] := by
      rintro rfl
      simp at hlen
    exact h1 c hc f ⟨hs, hp, hL2⟩ hdiv P hP hper hL2P w hne

end UnforcedLeray.Short.PartI
