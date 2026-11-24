import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2

/-!
# `WardX0SmoothInf` decomposed (`PartIII-b:IIIb-D2/3/2/11/2/2`, source 3604-3621, 4161-4186)

Source of record: `the November 2 reference manuscript`.
`wardX0SmoothInf_proved_of` derives `WardX0SmoothInf` from

* `SmoothOldSource` (parent file: the physical old source is a separated source with finite moment),
* `OldPhysSmooth` (source 3604-3621, 4161-4186: the physical old source of smooth old data is jointly
  `C^∞` in `(τ, z)` and vanishes for `|z|` large),
* `SepWSmoothTop` (source 3611-3621: all-order differentiation of `sepW` under the integral).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Leaf (A)** (source 3604-3621, 4161-4186, 3630-3640): for smooth old data `g` (compact support in
the open chart domain, `g = 0` for `νs ≤ 6/5`; so `g` vanishes near the seam `|q.2.1| = c/2` of
the floor in `chartOf`, and near `s = 0`), the physical old source `T = oldPhys R c g` is jointly
`C^∞` in `(τ, z) ∈ ℝ × Space` (the floor jumps of `chartOf` only occur at the seam, outside the
support of `g`, so the lift has local smooth branches) and vanishes for `|z|` large
(`T = 0` for `ϱ z > R√(5ν/6)` and for `|z| ≥ ρ₀`, `ρ₀` the height bound of `chartDom`). -/
def OldPhysSmooth : Prop :=
  ∀ (ν R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → IsSmoothOld c ν g →
    (∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => oldPhys R c g x.1 x.2 j k)) ∧
      ∃ Z : ℝ, ∀ τ z, Z < ‖z‖ → oldPhys R c g τ z = 0

/-- **Leaf (B)** (source 3604-3621): the all-order version of `SepWSmoothOn`.  For a `P`-periodic
separated source supported in `ϱ ≤ r_o` with finite moment, jointly `C^∞` in `(τ, z)` and
vanishing for `|z|` large, `(τ, y) ↦ W_μ(y, τ)` is `C^∞` on `ℝ × {ϱ > r_o}`: differentiate
`IIIa.sepW` under the integral to every order (induction on the order with
`hasFDerivAt_integral_of_dominated_of_fderiv_le`), with `|D^j∇K_t(x)| ≤ C_j|x|^{-4-j}`
(`IIIa.SepKernelBounds`), the gap `|y - λz| ≥ ϱ(y) - λϱ(z)`, and the `τ`-derivatives falling
on `T(z, τ + 2 log λ)` (bounded with all derivatives, supported in a bounded `z`-set). -/
def SepWSmoothTop : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    (∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k)) →
    (∃ Z : ℝ, ∀ τ z, Z < ‖z‖ → T τ z = 0) →
    ∀ i : Fin 3,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => IIIa.sepW ν μ T x.2 x.1 i)
        {x : ℝ × Space | rOut < ϱ x.2}

theorem wardX0SmoothInf_proved_of (hS : SmoothOldSource) (hA : OldPhysSmooth)
    (hB : SepWSmoothTop) : WardX0SmoothInf := by
  intro ν μ R c g hν hR hc hμ hg
  obtain ⟨hS1, hS2⟩ := hS ν R c g hν hR hc hg
  obtain ⟨hT, hZ⟩ := hA ν R c g hν hR hc hg
  have hro : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have key : ∀ (m : ℝ), -(1 / 4) < m → ∀ i : Fin 3,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × Space => (IIIa.sepW ν (m : ℂ) (oldPhys R c g) x.2 x.1 i).re)
        {x : ℝ × Space | x.2 ∈ youngOpen ν R} := fun m hm i =>
    Complex.reCLM.contDiff.comp_contDiffOn
      (hB ν (m : ℂ) _ _ _ hν (by simpa using hm) hro hP hS1 hS2 hT hZ i)
  rw [contDiffOn_euclidean]
  intro i
  have h1 := key μ hμ i
  have h2 := key (μ + 1) (by linarith) i
  refine (h1.sub h2).congr fun x _ => ?_
  simp [wardX0]

end UnforcedLeray.Short.PartIIIb.Concrete
