import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0CommWeakL2

/-!
# Part III-a, task `PartIII-a:T18/2/4/2/6`: `P0CommWeakC`

Target (`Sub/T18_2_4_2.lean`): `P0CommWeakC`. The complex weak derivative is split into real
and imaginary parts (`weak_reim_pc`), each part is a real weak derivative identity for the
`L²(cell)` classes of `reVec` / `imVec`, and `p0CommWeakL2` (the real form) gives the commutation.
The integrability clauses are `L²(cell)` times a cylinder test (`integrable_comp_test_pc`).
Source of record: `the November 2 reference manuscript`, lines 3442-3465.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem cellμ_eq_pc (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell B0579.cell
  rw [neg_div]

theorem reVec_apply_pc (f : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) (i : Fin 2) :
    reVec f x i = (f x i).re := by
  fin_cases i <;> rfl

theorem imVec_apply_pc (f : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) (i : Fin 2) :
    imVec f x i = (f x i).im := by
  fin_cases i <;> rfl

/-- A coordinate of an `L²(cell)` class is in `L²(cell)`. -/
theorem memLp_comp_pc {c : ℝ} (a : UnforcedLeray.Cyl.L2v c) (i : Fin 2) :
    MemLp (fun x => (a : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i) 2 (UnforcedLeray.Cyl.cellμ c) :=
  (EuclideanSpace.proj i : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).comp_memLp a

/-- An `L²(cell)` class coordinate times a cylinder test is integrable. -/
theorem integrable_comp_test_pc {c : ℝ} (a : UnforcedLeray.Cyl.L2v c) (i : Fin 2)
    {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.B0579.IsCylTest c φ) :
    Integrable (fun x => (a : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * φ x)
      (UnforcedLeray.Cyl.cellμ c) := by
  obtain ⟨R, hR⟩ := hφ.band
  have hφm : MemLp φ 2 (UnforcedLeray.Cyl.cellμ c) :=
    UnforcedLeray.Cyl.memLp_of_vanishes hφ.continuous hR 2
  exact (memLp_comp_pc a i).integrable_mul hφm

theorem integrable_comp_test_cell_pc {c : ℝ} (a : UnforcedLeray.Cyl.L2v c) (i : Fin 2)
    {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.B0579.IsCylTest c φ) :
    IntegrableOn (fun x => (a : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * φ x) (B0579.cell c) := by
  have h := integrable_comp_test_pc a i hφ
  unfold IntegrableOn
  rw [← cellμ_eq_pc]
  exact h

/-- Splitting a complex integrand `(A + iB) p` with real `A, B, p`. -/
theorem cplx_split_pc {μ : Measure (ℝ × ℝ)} (A B p : ℝ × ℝ → ℝ)
    (hA : Integrable (fun x => A x * p x) μ) (hB : Integrable (fun x => B x * p x) μ) :
    Integrable (fun x => ((A x : ℂ) + Complex.I * (B x : ℂ)) * (p x : ℂ)) μ ∧
      ∫ x, ((A x : ℂ) + Complex.I * (B x : ℂ)) * (p x : ℂ) ∂μ =
        ((∫ x, A x * p x ∂μ : ℝ) : ℂ) + Complex.I * ((∫ x, B x * p x ∂μ : ℝ) : ℂ) := by
  have e : (fun x => ((A x : ℂ) + Complex.I * (B x : ℂ)) * (p x : ℂ)) =
      fun x => ((A x * p x : ℝ) : ℂ) + Complex.I * ((B x * p x : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  have hA' : Integrable (fun x => ((A x * p x : ℝ) : ℂ)) μ := hA.ofReal
  have hB' : Integrable (fun x => Complex.I * ((B x * p x : ℝ) : ℂ)) μ :=
    (hB.ofReal).const_mul Complex.I
  rw [e]
  refine ⟨hA'.add hB', ?_⟩
  rw [integral_add hA' hB', integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

/-- Real and imaginary parts of a complex weak identity against a real test. -/
theorem weak_reim_pc {c : ℝ} {φ g : ℝ × ℝ → ℂ} {ψ p : ℝ × ℝ → ℝ}
    (hI1 : IntegrableOn (fun x => φ x * (p x : ℂ)) (B0579.cell c))
    (hI2 : IntegrableOn (fun x => g x * (ψ x : ℂ)) (B0579.cell c))
    (h : ∫ x in B0579.cell c, φ x * (p x : ℂ) = -∫ x in B0579.cell c, g x * (ψ x : ℂ)) :
    ∫ x in B0579.cell c, (φ x).re * p x = -∫ x in B0579.cell c, (g x).re * ψ x ∧
      ∫ x in B0579.cell c, (φ x).im * p x = -∫ x in B0579.cell c, (g x).im * ψ x := by
  have e1 : ∫ x in B0579.cell c, (φ x * (p x : ℂ)).re =
      (∫ x in B0579.cell c, φ x * (p x : ℂ)).re := integral_re hI1
  have e2 : ∫ x in B0579.cell c, (g x * (ψ x : ℂ)).re =
      (∫ x in B0579.cell c, g x * (ψ x : ℂ)).re := integral_re hI2
  have e3 : ∫ x in B0579.cell c, (φ x * (p x : ℂ)).im =
      (∫ x in B0579.cell c, φ x * (p x : ℂ)).im := integral_im hI1
  have e4 : ∫ x in B0579.cell c, (g x * (ψ x : ℂ)).im =
      (∫ x in B0579.cell c, g x * (ψ x : ℂ)).im := integral_im hI2
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at e1 e2 e3 e4
  constructor
  · rw [e1, h, Complex.neg_re, e2]
  · rw [e3, h, Complex.neg_im, e4]

theorem p0CommWeakC : UnforcedLeray.Short.IIIa.P0CommWeakC := by
  intro c hc f g hfr hfi hgr hgi hw
  obtain ⟨Fr, hFr⟩ : ∃ F : UnforcedLeray.Cyl.L2v c, F = hfr.toLp (reVec f) := ⟨_, rfl⟩
  obtain ⟨Fi, hFi⟩ : ∃ F : UnforcedLeray.Cyl.L2v c, F = hfi.toLp (imVec f) := ⟨_, rfl⟩
  obtain ⟨Wr, hWr⟩ : ∃ W : Fin 2 → UnforcedLeray.Cyl.L2v c,
      W = fun j => (hgr j).toLp (reVec (g j)) := ⟨_, rfl⟩
  obtain ⟨Wi, hWi⟩ : ∃ W : Fin 2 → UnforcedLeray.Cyl.L2v c,
      W = fun j => (hgi j).toLp (imVec (g j)) := ⟨_, rfl⟩
  have eTr : toL2v c (reVec f) = Fr := by
    rw [hFr]; unfold toL2v; rw [dif_pos hfr]
  have eTi : toL2v c (imVec f) = Fi := by
    rw [hFi]; unfold toL2v; rw [dif_pos hfi]
  have eTgr : ∀ j, toL2v c (reVec (g j)) = Wr j := by
    intro j; rw [hWr]; unfold toL2v; rw [dif_pos (hgr j)]
  have eTgi : ∀ j, toL2v c (imVec (g j)) = Wi j := by
    intro j; rw [hWi]; unfold toL2v; rw [dif_pos (hgi j)]
  have hPr : P0re c f = UnforcedLeray.Cyl.P0 c Fr := by unfold P0re; rw [eTr]
  have hPi : P0im c f = UnforcedLeray.Cyl.P0 c Fi := by unfold P0im; rw [eTi]
  have hPgr : ∀ j, P0re c (g j) = UnforcedLeray.Cyl.P0 c (Wr j) := fun j => by
    unfold P0re; rw [eTgr j]
  have hPgi : ∀ j, P0im c (g j) = UnforcedLeray.Cyl.P0 c (Wi j) := fun j => by
    unfold P0im; rw [eTgi j]
  -- real weak identities for the real parts
  have hwr : ∀ (j i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (Fr : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j ψ x =
        -∫ x in B0579.cell c, (Wr j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * ψ x := by
    intro j i ψ hψ
    have hI1 := ((hw i j).1 ψ hψ).1
    have hI2 := ((hw i j).1 ψ hψ).2
    have hreal : ∫ x in B0579.cell c, (f x i).re * B0579.pd j ψ x =
        -∫ x in B0579.cell c, (g j x i).re * ψ x :=
      (weak_reim_pc (φ := fun x => f x i) (g := fun x => g j x i) hI1 hI2
        ((hw i j).2 ψ hψ)).1
    have hcoord : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (Fr : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i = (f x i).re := by
      have h0 : (Fr : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) =ᵐ[volume.restrict (B0579.cell c)]
          reVec f := by
        rw [← cellμ_eq_pc, hFr]; exact MemLp.coeFn_toLp hfr
      filter_upwards [h0] with x hx
      rw [hx, reVec_apply_pc]
    have hcoordW : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (Wr j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i = (g j x i).re := by
      have h0 : (Wr j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) =ᵐ[volume.restrict (B0579.cell c)]
          reVec (g j) := by
        rw [← cellμ_eq_pc, hWr]; exact MemLp.coeFn_toLp (hgr j)
      filter_upwards [h0] with x hx
      rw [hx, reVec_apply_pc]
    have h1 : ∫ x in B0579.cell c, (Fr : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j ψ x =
        ∫ x in B0579.cell c, (f x i).re * B0579.pd j ψ x := by
      apply integral_congr_ae
      filter_upwards [hcoord] with x hx
      rw [hx]
    have h2 : ∫ x in B0579.cell c, (Wr j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * ψ x =
        ∫ x in B0579.cell c, (g j x i).re * ψ x := by
      apply integral_congr_ae
      filter_upwards [hcoordW] with x hx
      rw [hx]
    rw [h1, h2]
    exact hreal
  -- real weak identities for the imaginary parts
  have hwi : ∀ (j i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (Fi : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j ψ x =
        -∫ x in B0579.cell c, (Wi j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * ψ x := by
    intro j i ψ hψ
    have hI1 := ((hw i j).1 ψ hψ).1
    have hI2 := ((hw i j).1 ψ hψ).2
    have himag : ∫ x in B0579.cell c, (f x i).im * B0579.pd j ψ x =
        -∫ x in B0579.cell c, (g j x i).im * ψ x :=
      (weak_reim_pc (φ := fun x => f x i) (g := fun x => g j x i) hI1 hI2
        ((hw i j).2 ψ hψ)).2
    have hcoord : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (Fi : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i = (f x i).im := by
      have h0 : (Fi : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) =ᵐ[volume.restrict (B0579.cell c)]
          imVec f := by
        rw [← cellμ_eq_pc, hFi]; exact MemLp.coeFn_toLp hfi
      filter_upwards [h0] with x hx
      rw [hx, imVec_apply_pc]
    have hcoordW : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (Wi j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i = (g j x i).im := by
      have h0 : (Wi j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) =ᵐ[volume.restrict (B0579.cell c)]
          imVec (g j) := by
        rw [← cellμ_eq_pc, hWi]; exact MemLp.coeFn_toLp (hgi j)
      filter_upwards [h0] with x hx
      rw [hx, imVec_apply_pc]
    have h1 : ∫ x in B0579.cell c, (Fi : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j ψ x =
        ∫ x in B0579.cell c, (f x i).im * B0579.pd j ψ x := by
      apply integral_congr_ae
      filter_upwards [hcoord] with x hx
      rw [hx]
    have h2 : ∫ x in B0579.cell c, (Wi j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * ψ x =
        ∫ x in B0579.cell c, (g j x i).im * ψ x := by
      apply integral_congr_ae
      filter_upwards [hcoordW] with x hx
      rw [hx]
    rw [h1, h2]
    exact himag
  -- the projected real identities
  have R1 : ∀ (j i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, P0re c f x i * B0579.pd j ψ x =
        -∫ x in B0579.cell c, P0re c (g j) x i * ψ x := by
    intro j i ψ hψ
    rw [hPr, hPgr j]
    exact p0CommWeakL2 c hc Fr Wr hwr j i ψ hψ
  have R2 : ∀ (j i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, P0im c f x i * B0579.pd j ψ x =
        -∫ x in B0579.cell c, P0im c (g j) x i * ψ x := by
    intro j i ψ hψ
    rw [hPi, hPgi j]
    exact p0CommWeakL2 c hc Fi Wi hwi j i ψ hψ
  intro i j
  unfold HasWeakCellDerivC
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · have hA := integrable_comp_test_cell_pc (P0re c f) i (hψ.pd j)
    have hB := integrable_comp_test_cell_pc (P0im c f) i (hψ.pd j)
    exact (cplx_split_pc (μ := volume.restrict (B0579.cell c))
      (fun x => (P0re c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
      (fun x => (P0im c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
      (fun x => B0579.pd j ψ x) hA hB).1
  · have hA := integrable_comp_test_cell_pc (P0re c (g j)) i hψ
    have hB := integrable_comp_test_cell_pc (P0im c (g j)) i hψ
    exact (cplx_split_pc (μ := volume.restrict (B0579.cell c))
      (fun x => (P0re c (g j) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
      (fun x => (P0im c (g j) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
      (fun x => ψ x) hA hB).1
  · have hA := integrable_comp_test_cell_pc (P0re c f) i (hψ.pd j)
    have hB := integrable_comp_test_cell_pc (P0im c f) i (hψ.pd j)
    have hA' := integrable_comp_test_cell_pc (P0re c (g j)) i hψ
    have hB' := integrable_comp_test_cell_pc (P0im c (g j)) i hψ
    have sL : ∫ x in B0579.cell c, P0C c f x i * ((B0579.pd j ψ x : ℝ) : ℂ) =
        ((∫ x in B0579.cell c, P0re c f x i * B0579.pd j ψ x : ℝ) : ℂ) +
          Complex.I * ((∫ x in B0579.cell c, P0im c f x i * B0579.pd j ψ x : ℝ) : ℂ) :=
      (cplx_split_pc (μ := volume.restrict (B0579.cell c))
        (fun x => (P0re c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
        (fun x => (P0im c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
        (fun x => B0579.pd j ψ x) hA hB).2
    have sR : ∫ x in B0579.cell c, P0C c (g j) x i * ((ψ x : ℝ) : ℂ) =
        ((∫ x in B0579.cell c, P0re c (g j) x i * ψ x : ℝ) : ℂ) +
          Complex.I * ((∫ x in B0579.cell c, P0im c (g j) x i * ψ x : ℝ) : ℂ) :=
      (cplx_split_pc (μ := volume.restrict (B0579.cell c))
        (fun x => (P0re c (g j) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
        (fun x => (P0im c (g j) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i)
        (fun x => ψ x) hA' hB').2
    show ∫ x in B0579.cell c, P0C c f x i * ((B0579.pd j ψ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c, P0C c (g j) x i * ((ψ x : ℝ) : ℂ)
    rw [sL, sR, R1 j i ψ hψ, R2 j i ψ hψ]
    push_cast
    ring

end UnforcedLeray.Short.IIIa
