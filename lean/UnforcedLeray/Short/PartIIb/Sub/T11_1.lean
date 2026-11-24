import UnforcedLeray.Short.PartIIb.Sub.T11
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.Partition
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.AgeCell

/-!
# Part II-b, leaf `PartII-b:T11/1` (`FlatEqCellStream`): periodic stream tests (conditional)

Source of record: `the November 2 reference manuscript`. The flat equation
`(μ + S - ν s Δ_{q,η}) b = P_0 F` tested against planar solenoidal tests is SP 1923-1927
(`ProfileGraphFlat`, `StatementsFree.lean`); the planar Leray projection `P_0` is invisible on
`Ψ = ∇^⊥ψ`. The source never writes the passage from compactly supported tests to `q`-periodic
streams (it is the standard periodic unfolding, used silently at SP 1923-1938 and in the proof of
the free uniqueness invoked at SP 2328, 2618, 3575).

## Proof structure

For `ψ` smooth, `c`-periodic in `q`, supported in `σ ≤ s ≤ H`, `|η| ≤ L` (`σ > 0`), let `θ` be the
periodic partition of unity of `Tasks/FlatUnique/CellStream/Partition.lean`
(`Σ_n θ(q - n c) = 1`, `Σ_n θ^{(k)}(q - n c) = 0` for `k ≥ 1`; proved there, compiled).

1. `θψ` is a legitimate test, so `Ψ_θ = ∇^⊥(θψ)` is a planar solenoidal test
   (`CellStreamPlanarTest`), and the flat equation with `F = 0` gives
   `∫_{Coord} b · flatTranspose(Ψ_θ) = 0`.
2. (*Commutator.*) Pointwise, `b · flatTranspose(∇^⊥(θψ)) = Σ_{k=0}^{3} θ^{(k)}(q) G_k(x)` with
   `G_0 = b · flatTranspose(∇^⊥ψ)` and `G_1, G_2, G_3` explicit, linear in `b`, with
   `q`-periodic coefficients (`CellStreamCommutator`; checked by exact polynomial arithmetic).
3. (*Unfolding.*) Each `G_k` is a.e. `q`-periodic, vanishes outside `σ ≤ s ≤ H`, `|η| ≤ L`, and is
   locally integrable (from `b ∈ H_r`, `CellStreamCoeffs`), so `∫ θ^{(k)}(q) G_k = (Σ_n θ^{(k)}(·-nc))
   ∫_{cell} G_k` (`CoordPeriodicUnfold`): the `k ≥ 1` terms drop out and `∫_{cell} G_0 = 0`.
4. `ageμ c 0 = c⁻¹ · Lebesgue|_{(0,∞) × cell}` (`CellPart.ageμ_zero_eq`, proved) and `G_0 = 0` for
   `s < σ` give the cell form of the target.

Proved here: `flatEqCellStream_of` from `CellStreamPlanarTest`, `CellStreamCommutator`,
`CoordPeriodicUnfold`, `CellStreamCoeffs`. The leaf `HrBoxIntegrable` is the ingredient of
`CellStreamCoeffs`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `θ(q) ψ(s, q, η)`. -/
def qMul (θ : ℝ → ℝ) (ψ : Coord → ℝ) : Coord → ℝ := fun x => θ x.2.1 * ψ x

/-- The stream field `∇^⊥ψ = (∂_ηψ, -∂_qψ)` on the chart. -/
def streamField (ψ : Coord → ℝ) : Coord → Fin 2 → ℝ := fun y => ![cpd 2 ψ y, -cpd 1 ψ y]

/-- `G_0 = Σ_i b_i flatTranspose(∇^⊥ψ)_i`: the integrand of `FlatEqCellStream`. -/
def cellG0 (ν : ℝ) (μ : ℂ) (b : CProf) (ψ : Coord → ℝ) (x : Coord) : ℂ :=
  ∑ i : Fin 2, b x i * flatTranspose ν μ (streamField ψ) x i

/-- `G_1`, the coefficient of `θ'(q)`:
`b_0 · (-2νs ∂_q∂_ηψ) + b_1 · (-Λψ + 2νs ∂_q²ψ)` with
`Λψ = (μ-1)ψ - s∂_sψ - νs(∂_q²ψ + ∂_η²ψ)`. -/
def cellG1 (ν : ℝ) (μ : ℂ) (b : CProf) (ψ : Coord → ℝ) (x : Coord) : ℂ :=
  b x 0 * ((-(2 * ν * x.1 * cpd 1 (cpd 2 ψ) x) : ℝ) : ℂ) +
    b x 1 * (-((μ - 1) * (ψ x : ℂ) - ((x.1 * cpd 0 ψ x : ℝ) : ℂ) -
      ((ν * x.1 * (cpd 1 (cpd 1 ψ) x + cpd 2 (cpd 2 ψ) x) : ℝ) : ℂ)) +
      ((2 * ν * x.1 * cpd 1 (cpd 1 ψ) x : ℝ) : ℂ))

/-- `G_2`, the coefficient of `θ''(q)`: `b_0 · (-νs ∂_ηψ) + b_1 · (3νs ∂_qψ)`. -/
def cellG2 (ν : ℝ) (_μ : ℂ) (b : CProf) (ψ : Coord → ℝ) (x : Coord) : ℂ :=
  b x 0 * ((-(ν * x.1 * cpd 2 ψ x) : ℝ) : ℂ) + b x 1 * ((3 * ν * x.1 * cpd 1 ψ x : ℝ) : ℂ)

/-- `G_3`, the coefficient of `θ'''(q)`: `b_1 · (νs ψ)`. -/
def cellG3 (ν : ℝ) (_μ : ℂ) (b : CProf) (ψ : Coord → ℝ) (x : Coord) : ℂ :=
  b x 1 * ((ν * x.1 * ψ x : ℝ) : ℂ)

/-- The four coefficient profiles `G_0, …, G_3`. -/
def cellG (ν : ℝ) (μ : ℂ) (b : CProf) (ψ : Coord → ℝ) : Fin 4 → Coord → ℂ :=
  ![cellG0 ν μ b ψ, cellG1 ν μ b ψ, cellG2 ν μ b ψ, cellG3 ν μ b ψ]

/-- **Leaf `PartII-b:T11/1/1`** (`∇^⊥(θψ)` is a planar solenoidal test). For `θ` smooth with compact
support and `ψ` smooth supported in `σ ≤ s ≤ H`, `|η| ≤ L` (`σ > 0`), the field
`(∂_η(θψ), -∂_q(θψ))` is a planar solenoidal test: each component is smooth with compact support
inside `s > 0` (`tsupport ∂(θψ) ⊆ tsupport (θψ) ⊆ [σ, H] × supp θ × [-L, L]`), and
`∂_q∂_η(θψ) - ∂_η∂_q(θψ) = 0` by symmetry of second derivatives of a smooth function. -/
def CellStreamPlanarTest : Prop :=
  ∀ (θ : ℝ → ℝ) (ψ : Coord → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ → ContDiff ℝ ∞ ψ →
    (∃ σ H L : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → ψ x = 0) →
      IsPlanarSolTest (streamField (qMul θ ψ))

/-- **Leaf `PartII-b:T11/1/2`** (the commutator of `flatTranspose ∘ ∇^⊥` with multiplication by
`θ(q)`; pure calculus, identity checked by exact polynomial arithmetic). For smooth `θ`, `ψ` and
every function `b` (only the values `b x 0, b x 1` enter, linearly), at every point
`Σ_i b_i flatTranspose(∇^⊥(θψ))_i = Σ_{k=0}^{3} θ^{(k)}(q) G_k`. Proof: product rule for `cpd`
with `cpd 1 (θ(q)) = θ'(q)` and `cpd 0 (θ(q)) = cpd 2 (θ(q)) = 0`; component `0` of
`flatTranspose(∇^⊥(θψ))` equals `θ·T_0 - νs(2θ'∂_q∂_ηψ + θ''∂_ηψ)` and component `1` equals
`θ·T_1 - θ'Λψ + νs(2θ'∂_q²ψ + 3θ''∂_qψ + θ'''ψ)`, `T_i = flatTranspose(∇^⊥ψ)_i`. -/
def CellStreamCommutator : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (b : CProf) (θ : ℝ → ℝ) (ψ : Coord → ℝ),
    ContDiff ℝ ∞ θ → ContDiff ℝ ∞ ψ → ∀ x : Coord,
      ∑ i : Fin 2, b x i * flatTranspose ν μ (streamField (qMul θ ψ)) x i =
        ∑ k : Fin 4, ((iteratedDeriv (k : ℕ) θ x.2.1 : ℝ) : ℂ) * cellG ν μ b ψ k x

/-- **Leaf `PartII-b:T11/1/3`** (periodic unfolding on the chart `Coord = ℝ_s × ℝ_q × ℝ_η`). Let `h`
be continuous with compact support and `Σ_n h(q - n c) = P` for all `q`; let `G` be a.e.
`c`-periodic in `q`, vanishing outside `σ ≤ s ≤ H`, `|η| ≤ L`, and integrable on every box
`[σ, H] × [-R, R] × [-L, L]`. Then `h(q) G` is integrable on `Coord`, `G` is integrable on
`ℝ_s × cell`, and `∫ h(q) G = P ∫_{ℝ_s × cell} G` (`Cyl.cell c = [-c/2, c/2) × ℝ`).
Proof: Fubini over `(s, η)`; for a.e. `(s, η)` the slice is `c`-periodic in `q` and
`∫_ℝ h g = P ∫_cell g`, by `Lib/CylinderB/Periodize.lean` (`integral_cell_periodize_mul`) or
`Function.Periodic.intervalIntegral_add_eq` plus the finite cover of `supp h` by translates of the
cell. -/
def CoordPeriodicUnfold : Prop :=
  ∀ (c : ℝ) (h : ℝ → ℝ) (P : ℝ) (G : Coord → ℂ) (σ H L : ℝ),
    0 < c → Continuous h → HasCompactSupport h →
    (∀ q : ℝ, HasSum (fun n : ℤ => h (q - n * c)) P) →
    (∀ᵐ x : Coord, G (qShift c x) = G x) →
    (∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → G x = 0) →
    (∀ R : ℝ, IntegrableOn G (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume) →
      Integrable (fun x : Coord => (h x.2.1 : ℂ) * G x) volume ∧
      IntegrableOn G (univ ×ˢ Cyl.cell c) volume ∧
      ∫ x, (h x.2.1 : ℂ) * G x = (P : ℂ) * ∫ x in univ ×ˢ Cyl.cell c, G x

/-- **Leaf `PartII-b:T11/1/4`** (`H_r` box integrability). If `b ∈ H_r` (`r > 1`) then each component
of `b` is Lebesgue integrable on every box `[σ, H] × [-R, R] × [-L, L]` with `σ > 0`.
Proof: on `[σ, H]` the density `s^{r/2-5/2}` of `hMeas c r` is bounded above and below by positive
constants, so `∫_{[σ,H] × cell × [-L,L]} ‖b‖^r < ∞` (`InHr.finite`, `eLpNorm` to `lintegral`), hence
`‖b‖ ≤ 1 + ‖b‖^r` is integrable there (finite measure); `b` is Lebesgue
a.e.-strongly measurable on the box because it is `hMeas`-a.e. strongly measurable on
`s > 0, q ∈ cell` and a.e. `c`-periodic; the box is covered by finitely many `q`-translates of the
cell, `qShift` is measure preserving, and `b (qShift^n x) = b x` a.e.
(see `PartII-b:T07/6`, `T07/7` in `Sub/T07.lean` for the same periodization device). -/
def HrBoxIntegrable : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → InHr c r b →
    ∀ (σ H R L : ℝ), 0 < σ → ∀ i : Fin 2,
      IntegrableOn (fun x : Coord => b x i) (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume

/-- **Leaf `PartII-b:T11/1/5`** (the coefficient profiles; uses `T11/1/4`). For `b ∈ H_r` and `ψ`
smooth, `c`-periodic in `q`, supported in `σ ≤ s ≤ H`, `|η| ≤ L` (`σ > 0`), each `G_k`
(`k = 0, …, 3`) is a.e. `c`-periodic in `q`, vanishes where `s < σ`, `s > H` or `|η| > L`, and is
integrable on every box `[σ, H] × [-R, R] × [-L, L]`.
Proof: `G_k = Σ_i b_i · a_{k,i}` with coefficients `a_{k,i}` built from `s`, `ψ` and its `cpd`
derivatives up to order 2, hence continuous and (by periodicity of `ψ`) `q`-periodic; `ψ = 0` on the
open sets `s < σ`, `s > H`, `|η| > L`, so all derivatives of `ψ` vanish there; the box integrability
is `IntegrableOn.mul_continuousOn` for the compact box, using `HrBoxIntegrable`. -/
def CellStreamCoeffs : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (ψ : Coord → ℝ), 0 < c → 1 < r → InHr c r b →
    ContDiff ℝ ∞ ψ → (∀ x, ψ (qShift c x) = ψ x) →
    ∀ (σ H L : ℝ), 0 < σ → (∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → ψ x = 0) →
      ∀ k : Fin 4,
        (∀ᵐ x : Coord, cellG ν μ b ψ k (qShift c x) = cellG ν μ b ψ k x) ∧
        (∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → cellG ν μ b ψ k x = 0) ∧
        (∀ R : ℝ, IntegrableOn (cellG ν μ b ψ k) (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume)

/-- Iterated derivatives of a smooth compactly supported function are continuous with compact
support. -/
theorem iteratedDeriv_compact {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (k : ℕ) : Continuous (iteratedDeriv k θ) ∧ HasCompactSupport (iteratedDeriv k θ) := by
  refine ⟨hθ.continuous_iteratedDeriv k (by simp), ?_⟩
  induction k with
  | zero => simpa [iteratedDeriv_zero] using hc
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- **Cell form of the flat equation with periodic streams** (`PartII-b:T11/1`, conditional). -/
theorem flatEqCellStream_of (hA : CellStreamPlanarTest) (hB : CellStreamCommutator)
    (hU : CoordPeriodicUnfold) (hC : CellStreamCoeffs) : FlatEqCellStream := by
  intro c r ν μ b hc hν hr hb h0 ψ hψ hψper hvan
  obtain ⟨σ, H, L, hσ, hv⟩ := hvan
  obtain ⟨θ, hθ, hθc, -, hθ1, hθk⟩ := CellPart.exists_partition_of_derivs hc
  -- the legitimate test `∇^⊥(θψ)`
  have htest : IsPlanarSolTest (streamField (qMul θ ψ)) := hA θ ψ hθ hθc hψ ⟨σ, H, L, hσ, hv⟩
  obtain ⟨-, -, heq⟩ := h0.equation _ htest
  have h00 : ∫ x, cdot (0 : CProf) (streamField (qMul θ ψ)) x = 0 := by
    simp [cdot]
  rw [h00] at heq
  -- coefficients
  have hP := hC c r ν μ b ψ hc hr hb hψ hψper σ H L hσ hv
  -- unfolding of each piece
  have hpiece : ∀ k : Fin 4,
      Integrable (fun x : Coord => ((iteratedDeriv (k : ℕ) θ x.2.1 : ℝ) : ℂ) * cellG ν μ b ψ k x)
          volume ∧
        ∫ x, ((iteratedDeriv (k : ℕ) θ x.2.1 : ℝ) : ℂ) * cellG ν μ b ψ k x =
          ((if (k : ℕ) = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) *
            ∫ x in univ ×ˢ Cyl.cell c, cellG ν μ b ψ k x := by
    intro k
    obtain ⟨hk1, hk2, hk3⟩ := hP k
    obtain ⟨hcont, hcs⟩ := iteratedDeriv_compact hθ hθc (k : ℕ)
    by_cases hk0 : (k : ℕ) = 0
    · have hsum : ∀ q : ℝ, HasSum (fun n : ℤ => iteratedDeriv (k : ℕ) θ (q - n * c)) 1 := by
        intro q
        rw [hk0, iteratedDeriv_zero]
        exact hθ1 q
      obtain ⟨i1, -, i3⟩ := hU c _ 1 _ σ H L hc hcont hcs hsum hk1 hk2 hk3
      refine ⟨i1, ?_⟩
      rw [i3]
      simp [hk0]
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
      have hsum : ∀ q : ℝ, HasSum (fun n : ℤ => iteratedDeriv (k : ℕ) θ (q - n * c)) 0 := by
        intro q
        rw [hj]
        exact hθk j q
      obtain ⟨i1, -, i3⟩ := hU c _ 0 _ σ H L hc hcont hcs hsum hk1 hk2 hk3
      refine ⟨i1, ?_⟩
      rw [i3]
      simp [hk0]
  -- assemble: the sum of the four pieces integrates to the cell integral of `G_0`
  have hdec : (fun x : Coord => ∑ i : Fin 2, b x i * flatTranspose ν μ (streamField (qMul θ ψ)) x i) =
      fun x => ∑ k : Fin 4, ((iteratedDeriv (k : ℕ) θ x.2.1 : ℝ) : ℂ) * cellG ν μ b ψ k x := by
    funext x
    exact hB ν μ b θ ψ hθ hψ x
  rw [hdec, integral_finsetSum _ (fun k _ => (hpiece k).1)] at heq
  simp only [(hpiece _).2, Fin.sum_univ_four] at heq
  have hJ : ∫ x in univ ×ˢ Cyl.cell c, cellG ν μ b ψ 0 x = 0 := by
    simpa using heq
  -- pass to the measure `ageμ c 0`
  have hG0 : ∀ x : Coord, x ∈ (univ ×ˢ Cyl.cell c) \ (Ioi (0 : ℝ) ×ˢ Cyl.cell c) →
      cellG ν μ b ψ 0 x = 0 := by
    intro x hx
    have hx1 : x.1 ≤ 0 := by
      by_contra hpos
      exact hx.2 ⟨not_le.1 hpos, hx.1.2⟩
    exact (hP 0).2.1 x (Or.inl (lt_of_le_of_lt hx1 hσ))
  have hmeasT : MeasurableSet (univ ×ˢ Cyl.cell c : Set Coord) :=
    MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hsub : (Ioi (0 : ℝ) ×ˢ Cyl.cell c : Set Coord) ⊆ univ ×ˢ Cyl.cell c := by
    intro x hx; exact ⟨mem_univ _, hx.2⟩
  have hres : ∫ x in Ioi (0 : ℝ) ×ˢ Cyl.cell c, cellG ν μ b ψ 0 x = 0 := by
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasT hsub hG0]
    exact hJ
  show ∫ x, cellG0 ν μ b ψ x ∂(Axi.ageμ c 0) = 0
  rw [CellPart.ageμ_zero_eq, integral_smul_measure]
  have hres' : ∫ x in Ioi (0 : ℝ) ×ˢ Cyl.cell c, cellG0 ν μ b ψ x = 0 := hres
  rw [hres', smul_zero]

end UnforcedLeray.Short.IIb
