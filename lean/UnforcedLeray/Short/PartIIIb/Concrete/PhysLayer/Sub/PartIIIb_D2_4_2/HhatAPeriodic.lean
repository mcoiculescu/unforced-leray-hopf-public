import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs

/-!
# Lattice periodicity of `ĥ_A` (source 4963-4985, 4991-4997)

The Gaussians `V_j, p_j, ψ_j` depend on `q` only through `x_j = (q - jc, η)`, so a shift
`q ↦ q + nc` reindexes the lattice sums over `j ∈ ℤ` (`Equiv.tsum_eq`); the derivatives
commute with the translation (`fderiv_comp_add_right`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `x_j` at a shifted point is `x_{j-n}` at the original point. -/
theorem hper_xj_shift (ν : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    xj ν j (y.1 + (n : ℝ) * cOf ν, y.2) = xj ν (j - n) y := by
  unfold xj
  ext <;> simp <;> ring

theorem hper_psij_shift (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    psij ν s j (y.1 + (n : ℝ) * cOf ν, y.2) = psij ν s (j - n) y := by
  unfold psij
  rw [hper_xj_shift]

theorem hper_Vj_shift (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    Vj ν s j (y.1 + (n : ℝ) * cOf ν, y.2) = Vj ν s (j - n) y := by
  unfold Vj
  rw [hper_xj_shift]

/-- Derivative of a translated-and-reindexed function. -/
theorem hper_fderiv_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ × ℝ → E) (a : ℝ) (h : ∀ y : ℝ × ℝ, f (y.1 + a, y.2) = g y) (x : ℝ × ℝ) :
    fderiv ℝ f (x.1 + a, x.2) = fderiv ℝ g x := by
  have hx : ((x.1 + a, x.2) : ℝ × ℝ) = x + (a, 0) := by
    ext <;> simp
  have hg : g = fun y => f (y + (a, 0)) := by
    funext y
    rw [← h y]
    congr 1
    ext <;> simp
  rw [hx, hg, fderiv_comp_add_right]

/-- Reindexing a lattice sum under the shift. -/
theorem hper_tsum_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (n : ℤ) (T : ℤ → ℝ × ℝ → E)
    (hT : ∀ (j : ℤ) (y : ℝ × ℝ), T j (y.1 + a, y.2) = T (j - n) y) (x : ℝ × ℝ) :
    ∑' j, T j (x.1 + a, x.2) = ∑' j, T j x := by
  rw [tsum_congr (fun j => hT j x)]
  exact Equiv.tsum_eq (Equiv.subRight n) (fun j => T j x)

/-- Invariance of `ψ^p_A` under `q ↦ q + nc`. -/
theorem hper_psipA_shift (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ) (x : ℝ × ℝ) :
    psipA ν χ A s (x.1 + (n : ℝ) * cOf ν, x.2) = psipA ν χ A s x := by
  unfold psipA
  refine hper_tsum_shift ((n : ℝ) * cOf ν) n
    (fun j y => merTrace (Ay ν χ A s) * psij ν s j y
      - fderiv ℝ (psij ν s j) y (merApply (Ay ν χ A s) (xj ν j y))) ?_ x
  intro j y
  rw [hper_psij_shift ν s n j y,
    hper_fderiv_shift (psij ν s j) (psij ν s (j - n)) _ (hper_psij_shift ν s n j) y,
    hper_xj_shift ν n j y]

/-- Invariance of `h^p_A` under `q ↦ q + nc`. -/
theorem hper_hpA_shift (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ) (x : ℝ × ℝ) :
    hpA ν χ A s (x.1 + (n : ℝ) * cOf ν, x.2) = hpA ν χ A s x := by
  unfold hpA
  refine hper_tsum_shift ((n : ℝ) * cOf ν) n
    (fun j y => merApply (Ay ν χ A s) (Vj ν s j y)
      - fderiv ℝ (Vj ν s j) y (merApply (Ay ν χ A s) (xj ν j y))) ?_ x
  intro j y
  rw [hper_Vj_shift ν s n j y,
    hper_fderiv_shift (Vj ν s j) (Vj ν s (j - n)) _ (hper_Vj_shift ν s n j) y,
    hper_xj_shift ν n j y]

/-- Invariance of the Kop-term of `ĥ_A` under `q ↦ q + nc`. -/
theorem hper_Kop_shift (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ) (x : ℝ × ℝ) :
    Kop (fun s' y => psipA ν χ A s' y) s (x.1 + (n : ℝ) * cOf ν, x.2) =
      Kop (fun s' y => psipA ν χ A s' y) s x := by
  have hf : fderiv ℝ (psipA ν χ A s) (x.1 + (n : ℝ) * cOf ν, x.2) = fderiv ℝ (psipA ν χ A s) x :=
    hper_fderiv_shift (psipA ν χ A s) (psipA ν χ A s) _ (hper_psipA_shift ν χ A s n) x
  have hd : (fun s' => psipA ν χ A s' (x.1 + (n : ℝ) * cOf ν, x.2)) =
      (fun s' => psipA ν χ A s' x) :=
    funext (fun s' => hper_psipA_shift ν χ A s' n x)
  unfold Kop
  dsimp only
  rw [hf, hd]

/-- **Lattice periodicity** (source 4963-4985): `ĥ_A` is invariant under `q ↦ q + n c`. -/
theorem hhatAPeriodic_proof (ν ε : ℝ) (χf : ℝ → ℝ) : HhatAPeriodic ν ε χf := by
  intro A s x n
  unfold hhatA
  rw [hper_hpA_shift ν χf A s n x, hper_psipA_shift ν χf A s n x,
    hper_Kop_shift ν χf A s n x]

end UnforcedLeray.Short.PartIIIb.Concrete
