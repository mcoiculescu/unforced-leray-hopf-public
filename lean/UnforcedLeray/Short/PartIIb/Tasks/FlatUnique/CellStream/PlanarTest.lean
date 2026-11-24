import UnforcedLeray.Short.PartIIb.Sub.T11_1

/-!
# Part II-b, task `PartII-b:T11/1/1` (`CellStreamPlanarTest`): the stream field of a cell-cut
test is a planar solenoidal test

Source of record: `the November 2 reference manuscript`; the planar solenoidal
condition is `IsPlanarSolTest` (`Defs.lean`), the statement is `CellStreamPlanarTest`
(`Sub/T11_1.lean`).

Proof. For `Φ(s, q, η) = θ(q) ψ(s, q, η)`:
1. `Φ` is smooth, and its support lies in the compact box `[σ, H] × tsupport θ × [-L, L]`, which is
   contained in `{s > 0}` because `σ > 0`.
2. The components of `∇^⊥Φ = (∂_ηΦ, -∂_qΦ)` are coordinate tests, since a directional derivative of
   a test function is a test function with support inside the support of the function.
3. `∂_q(∂_ηΦ) + ∂_η(-∂_qΦ) = 0` is the symmetry of second derivatives of a `C^∞` function.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The partial derivative `y ↦ ∂_v φ(y)` of a smooth function has Fréchet derivative
`(D²φ(x)).flip v`. -/
theorem planarTest_hasFDerivAt_partial {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (v x : Coord) :
    HasFDerivAt (fun y => fderiv ℝ φ y v) ((fderiv ℝ (fderiv ℝ φ) x).flip v) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((ContDiff.fderiv_right (m := ∞) hφ (by simp)).differentiable (by simp)) x
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  simpa using h

/-- A directional derivative of a coordinate test is a coordinate test. -/
theorem planarTest_isCoordTest_partial {φ : Coord → ℝ} (hφ : IsCoordTest φ) (v : Coord) :
    IsCoordTest (fun x => fderiv ℝ φ x v) :=
  ⟨(ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)).clm_apply contDiff_const,
    hφ.compact.fderiv_apply (𝕜 := ℝ) v,
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) v).trans hφ.supp⟩

/-- The negative of a coordinate test is a coordinate test. -/
theorem planarTest_isCoordTest_neg {g : Coord → ℝ} (h : IsCoordTest g) :
    IsCoordTest (fun x => -g x) := by
  have hsub : Function.support (fun x => -g x) ⊆ Function.support g := by
    intro x hx
    show g x ≠ 0
    intro h0
    exact (Function.mem_support.1 hx) (by simp [h0])
  refine ⟨h.smooth.neg, h.compact.neg, ?_⟩
  exact (closure_minimal (hsub.trans (subset_tsupport g)) (isClosed_tsupport g)).trans h.supp

/-- Symmetry of mixed second derivatives: `∂_q ∂_η φ - ∂_η ∂_q φ = 0` for smooth `φ`, written in
the form that appears in the divergence of `(∂_ηφ, -∂_qφ)`. -/
theorem planarTest_div_free {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    fderiv ℝ (fun y => fderiv ℝ φ y (cdir 2)) x (cdir 1) +
      fderiv ℝ (fun y => -(fderiv ℝ φ y (cdir 1))) x (cdir 2) = 0 := by
  have hsymm : IsSymmSndFDerivAt ℝ φ x := hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  have hA : fderiv ℝ (fun y => fderiv ℝ φ y (cdir 2)) x (cdir 1) =
      fderiv ℝ (fderiv ℝ φ) x (cdir 1) (cdir 2) := by
    rw [(planarTest_hasFDerivAt_partial hφ (cdir 2) x).fderiv]
    rfl
  have hB : fderiv ℝ (fun y => -(fderiv ℝ φ y (cdir 1))) x (cdir 2) =
      -(fderiv ℝ (fderiv ℝ φ) x (cdir 2) (cdir 1)) := by
    rw [(planarTest_hasFDerivAt_partial hφ (cdir 1) x).fun_neg.fderiv]
    rfl
  rw [hA, hB, hsymm (cdir 1) (cdir 2)]
  ring

/-- **Leaf `PartII-b:T11/1/1`**. For `θ` smooth with compact support and `ψ` smooth with
`ψ = 0` whenever `s < σ`, `H < s` or `L < |η|` (`σ > 0`), the field `∇^⊥(θψ)` is a planar
solenoidal test. -/
theorem cellStreamPlanarTest : CellStreamPlanarTest := by
  unfold CellStreamPlanarTest
  intro θ ψ hθ hθc hψ hsig
  obtain ⟨σ, H, L, hσ, hψ0⟩ := hsig
  have hK : IsCompact (Icc σ H ×ˢ (tsupport θ ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod ((show IsCompact (tsupport θ) from hθc).prod isCompact_Icc)
  have hsub : Function.support (qMul θ ψ) ⊆ Icc σ H ×ˢ (tsupport θ ×ˢ Icc (-L) L) := by
    intro x hx
    have hne : qMul θ ψ x ≠ 0 := hx
    have hθne : θ x.2.1 ≠ 0 := fun h => hne (by simp [qMul, h])
    have hψne : ψ x ≠ 0 := fun h => hne (by simp [qMul, h])
    have hgood : ¬ (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) := fun h => hψne (hψ0 x h)
    simp only [not_or, not_lt] at hgood
    obtain ⟨h1, h2, h3⟩ := hgood
    have hθmem : x.2.1 ∈ Function.support θ := hθne
    exact ⟨⟨h1, h2⟩, subset_tsupport θ hθmem, abs_le.1 h3⟩
  have htsub : tsupport (qMul θ ψ) ⊆ Icc σ H ×ˢ (tsupport θ ×ˢ Icc (-L) L) :=
    closure_minimal hsub hK.isClosed
  have hφ : IsCoordTest (qMul θ ψ) := by
    refine ⟨?_, ?_, ?_⟩
    · have h2 : ContDiff ℝ ∞ (fun x : Coord => x.2.1) := contDiff_fst.comp contDiff_snd
      have hsm : ContDiff ℝ ∞ (fun x : Coord => θ x.2.1) := hθ.comp h2
      exact hsm.mul hψ
    · exact hK.of_isClosed_subset (isClosed_tsupport _) htsub
    · intro x hx
      exact ⟨lt_of_lt_of_le hσ (htsub hx).1.1, mem_univ _⟩
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact planarTest_isCoordTest_partial hφ (cdir 2)
    · exact planarTest_isCoordTest_neg (planarTest_isCoordTest_partial hφ (cdir 1))
  · intro x
    exact planarTest_div_free hφ.smooth x

end UnforcedLeray.Short.IIb
