import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_6

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest)
open UnforcedLeray.Short.PartIIa (pdS pdQ pdEta)

/-- A function invariant under translation by `a` has invariant directional derivatives. -/
theorem fderiv_apply_add_of_inv_cellPt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Profile → E) (a : Profile) (hf : ∀ x, f (x + a) = f x) (x v : Profile) :
    fderiv ℝ f (x + a) v = fderiv ℝ f x v := by
  have h1 : fderiv ℝ (fun y => f (y + a)) x = fderiv ℝ f (x + a) := fderiv_comp_add_right a
  have h2 : (fun y => f (y + a)) = f := funext hf
  rw [h2] at h1
  rw [← h1]

/-- The resolvent test `(μ - A₀*)ζ` is invariant under the `q`-translation `(0, -c, 0)` when `ζ`
is. -/
theorem resolventTest_add_cellPt (ν μ c : ℝ) (ζ : Profile → MeridC)
    (hζ : ∀ x, ζ (x + (0, -c, 0)) = ζ x) (x : Profile) :
    resolventTest ν μ ζ (x + (0, -c, 0)) = resolventTest ν μ ζ x := by
  have hS : ∀ y, pdS ζ (y + (0, -c, 0)) = pdS ζ y := fun y =>
    fderiv_apply_add_of_inv_cellPt ζ _ hζ y (1, 0, 0)
  have hQ : ∀ y, pdQ ζ (y + (0, -c, 0)) = pdQ ζ y := fun y =>
    fderiv_apply_add_of_inv_cellPt ζ _ hζ y (0, 1, 0)
  have hE : ∀ y, pdEta ζ (y + (0, -c, 0)) = pdEta ζ y := fun y =>
    fderiv_apply_add_of_inv_cellPt ζ _ hζ y (0, 0, 1)
  have hQQ : ∀ y, pdQ (pdQ ζ) (y + (0, -c, 0)) = pdQ (pdQ ζ) y := fun y =>
    fderiv_apply_add_of_inv_cellPt (pdQ ζ) _ hQ y (0, 1, 0)
  have hEE : ∀ y, pdEta (pdEta ζ) (y + (0, -c, 0)) = pdEta (pdEta ζ) y := fun y =>
    fderiv_apply_add_of_inv_cellPt (pdEta ζ) _ hE y (0, 0, 1)
  have h0 : (x + (0, -c, 0)).1 = x.1 := by simp
  unfold resolventTest A0adj
  rw [h0, hζ, hS, hQQ, hEE]

/-- `ζ_Φ = s^{1/2}Φ` is invariant under the `q`-shift by `c` when `Φ` is `c`-periodic. -/
theorem zetaPhi_add_cellPt (c : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : IsFlatTest c Φ)
    (x : Profile) : zetaPhi Φ (x + (0, -c, 0)) = zetaPhi Φ x := by
  obtain ⟨s, q, η⟩ := x
  have hper : ∀ i, Φ s (q + -c, η) i = Φ s (q, η) i := by
    intro i
    have := hΦ.periodic s (q + -c, η) i
    simpa using this.symm
  unfold zetaPhi
  congr 1
  funext i
  simp [hper]

/-- Leaf 4 (`c`-periodicity in `q`, `cellPt` shifts `q` by `0` or `-c`): the tests are invariant
under `cellPt`. -/
theorem zetaPhiCellPtInvariant : ZetaPhiCellPtInvariant := by
  intro c ν μ Φ hΦ p
  by_cases h : p.2.1 < c / 2
  · have hc : NearInst.cellPt c p = p := by
      simp [NearInst.cellPt, h]
    rw [hc]
    exact ⟨rfl, rfl⟩
  · have hc : NearInst.cellPt c p = p + (0, -c, 0) := by
      have h' : NearInst.cellPt c p = (p.1, p.2.1 + -c, p.2.2) := by
        simp [NearInst.cellPt, h, sub_eq_add_neg]
      rw [h']
      exact Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [hc]
    exact ⟨zetaPhi_add_cellPt c Φ hΦ p,
      resolventTest_add_cellPt ν μ c (zetaPhi Φ) (zetaPhi_add_cellPt c Φ hΦ) p⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
