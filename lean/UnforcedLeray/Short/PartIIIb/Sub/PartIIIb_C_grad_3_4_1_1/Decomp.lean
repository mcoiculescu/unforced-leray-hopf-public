import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1

/-!
# Decomposition of `GradLatticeHp` and `GradLatticePsi` into termwise leaves

Source `the November 2 reference manuscript`
4963-4980 (`V_j, p_j, ψ_j`, `h^p_A`, `ψ^p_A`), 5036-5039, 5063-5079.

Both lattice envelopes follow from three kinds of leaves:
* `GradLatticeSummable`: `Σ_j W(x₁ - jc, x₂)` is summable (Gaussian lattice sum);
* termwise envelopes (`GradHpTermEnv`, `GradPsiTermEnv`): each lattice term and its `∂_q, ∂_η, 𝒦`
  (and `∂𝒦, 𝒦²` for `ψ`) is `≤ C·gradF·W(x - jc)` (source 5063-5079);
* termwise differentiation (`GradHpTsum`, `GradPsiTsum`): the operators commute with the lattice
  sum (`HasSum` of the termwise images to the image of the sum).
Proved: `gradLatticeHp_of`, `gradLatticePsi_of`.
-/

set_option autoImplicit false

noncomputable section

open Set UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th Gaussian weight at `x`. -/
def gradW (ν : ℝ) (x : ℝ × ℝ) (j : ℤ) : ℝ :=
  latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2

/-- Component `i` (`0 ↦ r`, `1 ↦ z`) of `h^p_A`. -/
def gradHpU (i : Fin 2) (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → ℝ × ℝ → ℝ :=
  if i = 0 then hpR ν χf A else hpZ ν χf A

/-- Component `i` of the `j`-th lattice term of `h^p_A` as a function of `(s, x)`. -/
def gradHpTm (i : Fin 2) (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) : ℝ → ℝ × ℝ → ℝ :=
  fun s' y => if i = 0 then (hpATerm ν χf A s' y j).1 else (hpATerm ν χf A s' y j).2

/-- The `j`-th lattice term of `ψ^p_A` as a function of `(s, x)`. -/
def gradPsiTm (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) : ℝ → ℝ × ℝ → ℝ :=
  fun s' y => psipATerm ν χf A s' y j

/-- The seven operators applied to `ψ^p_A` in `GradLatticePsi`:
`id, ∂_q, ∂_η, 𝒦, ∂_q𝒦, ∂_η𝒦, 𝒦²`. -/
def gradPsiOps : Fin 7 → (ℝ → ℝ × ℝ → ℝ) → ℝ → ℝ × ℝ → ℝ :=
  ![fun u => u, fun u => dQ u, fun u => dEta u, fun u => Kop u,
    fun u => dQ (fun s' y => Kop u s' y), fun u => dEta (fun s' y => Kop u s' y),
    fun u => Kop (fun s' y => Kop u s' y)]

/-- Leaf C: the Gaussian lattice sum converges (spacing `c > 0`). -/
def GradLatticeSummable : Prop :=
  ∀ c : ℝ, 0 < c → ∀ x : ℝ × ℝ,
    Summable (fun j : ℤ => latticeW gradAlpha gradK (x.1 - (j : ℝ) * c) x.2)

/-- Leaf A (`h^p`): termwise envelope of the lattice terms of `h^p_A` and their `∂_q, ∂_η, 𝒦`
(source 4973, 5063-5079). -/
def GradHpTermEnv : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2) (j : ℤ),
      |gradHpTm i ν χf A j s x| ≤ C * gradF ν χf A s * gradW ν x j ∧
      |dQ (gradHpTm i ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j ∧
      |dEta (gradHpTm i ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j ∧
      |Kop (gradHpTm i ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j

/-- Leaf B (`h^p`): `∂_q, ∂_η, 𝒦` commute with the lattice sum defining `h^p_A`. -/
def GradHpTsum : Prop :=
  ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2),
      HasSum (fun j => gradHpTm i ν χf A j s x) (gradHpU i ν χf A s x) ∧
      HasSum (fun j => dQ (gradHpTm i ν χf A j) s x) (dQ (gradHpU i ν χf A) s x) ∧
      HasSum (fun j => dEta (gradHpTm i ν χf A j) s x) (dEta (gradHpU i ν χf A) s x) ∧
      HasSum (fun j => Kop (gradHpTm i ν χf A j) s x) (Kop (gradHpU i ν χf A) s x)

/-- Leaf A (`ψ^p`): termwise envelope of the lattice terms of `ψ^p_A` under the seven operators
(source 4974-4975, 5063-5079). -/
def GradPsiTermEnv : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (m : Fin 7) (j : ℤ),
      |gradPsiOps m (gradPsiTm ν χf A j) s x| ≤ C * gradF ν χf A s * gradW ν x j

/-- Leaf B (`ψ^p`): the seven operators commute with the lattice sum defining `ψ^p_A`. -/
def GradPsiTsum : Prop :=
  ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (m : Fin 7),
      HasSum (fun j => gradPsiOps m (gradPsiTm ν χf A j) s x)
        (gradPsiOps m (psipA ν χf A) s x)

/-- A sum bounded termwise by a summable family is bounded by the sum of the bounds. -/
theorem abs_le_latticeS_of_hasSum {ν : ℝ} {x : ℝ × ℝ} {B a : ℝ} {f : ℤ → ℝ}
    (hB : 0 ≤ B) (hsum : Summable (gradW ν x)) (hs : HasSum f a)
    (hb : ∀ j, |f j| ≤ B * gradW ν x j) :
    |a| ≤ B * latticeS gradAlpha gradK (cOf ν) x := by
  have h1 : HasSum (fun j => B * gradW ν x j) (B * ∑' j, gradW ν x j) := hsum.hasSum.mul_left B
  have h2 := tsum_of_norm_bounded h1 (f := f) (fun j => by simpa using hb j)
  rw [← hs.tsum_eq]
  simpa [latticeS, gradW] using h2

theorem gradW_summable (hL : GradLatticeSummable) (ν : ℝ) (hν : 0 < ν) (x : ℝ × ℝ) :
    Summable (gradW ν x) :=
  hL (cOf ν) (by unfold cOf; positivity) x

theorem gradF_nonneg (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) : 0 ≤ gradF ν χf A s := by
  unfold gradF frob; positivity

theorem gradLatticeHp_of (hC : GradLatticeSummable) (hA : GradHpTermEnv) (hB : GradHpTsum) :
    GradLatticeHp := by
  obtain ⟨C, hC0, hE⟩ := hA
  refine ⟨C, hC0, ?_⟩
  intro ν s χf A hd x u hu
  have hν : 0 < ν := hd.1
  have hBn : 0 ≤ C * gradF ν χf A s := mul_nonneg hC0 (gradF_nonneg _ _ _ _)
  have hsum := gradW_summable hC ν hν x
  obtain ⟨i, rfl⟩ : ∃ i : Fin 2, u = gradHpU i ν χf A := by
    rcases hu with rfl | rfl
    · exact ⟨0, by simp [gradHpU]⟩
    · exact ⟨1, by simp [gradHpU]⟩
  obtain ⟨h0, h1, h2, h3⟩ := hB ν s χf A hd x i
  have e := fun j => hE ν s χf A hd x i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact abs_le_latticeS_of_hasSum hBn hsum h0 (fun j => (e j).1)
  · exact abs_le_latticeS_of_hasSum hBn hsum h1 (fun j => (e j).2.1)
  · exact abs_le_latticeS_of_hasSum hBn hsum h2 (fun j => (e j).2.2.1)
  · exact abs_le_latticeS_of_hasSum hBn hsum h3 (fun j => (e j).2.2.2)

theorem gradLatticePsi_of (hC : GradLatticeSummable) (hA : GradPsiTermEnv) (hB : GradPsiTsum) :
    GradLatticePsi := by
  obtain ⟨C, hC0, hE⟩ := hA
  refine ⟨C, hC0, ?_⟩
  intro ν s χf A hd x
  have hν : 0 < ν := hd.1
  have hBn : 0 ≤ C * gradF ν χf A s := mul_nonneg hC0 (gradF_nonneg _ _ _ _)
  have hsum := gradW_summable hC ν hν x
  have key : ∀ m : Fin 7, |gradPsiOps m (psipA ν χf A) s x| ≤
      C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x := fun m =>
    abs_le_latticeS_of_hasSum hBn hsum (hB ν s χf A hd x m) (fun j => hE ν s χf A hd x m j)
  exact ⟨key 0, key 1, key 2, key 3, key 4, key 5, key 6⟩

end UnforcedLeray.Short.PartIIIb.Concrete
