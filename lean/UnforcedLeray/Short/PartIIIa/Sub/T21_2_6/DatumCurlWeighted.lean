import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.Spine.Proofs.EstDerivWordBridge

/-!
# Part III-a, `PartIII-a:T21/2/6/7`: weighted bound of the periodized unit Gaussian vorticity

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2867 and
327-336. Given the lattice representation of every word derivative of `curl datum_d`
(`DatumCurlLattice`) and the weighted bound of centred lattice sums (`CenteredLatticeWeighted`),
each word derivative of order `j` satisfies `⟨y⟩^{2k}|D_w curl datum_d(y)| ≤ C` on `C_d`, `d ≥ 1`,
with one constant over the finitely many words of length `j` (`B0147.uniform_words`). The bridge
`Spine.norm_iteratedFDeriv_le_of_derivWord` then gives `‖D^j curl datum_d(y)‖ ≤ 2^j C ⟨y⟩^{-2k}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The curl of a `C^∞` vector field is `C^∞` (curl = `∂_q u₂ - ∂_η u₁`). -/
theorem dcw_contDiff_curl {F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (UnforcedLeray.Cyl.curl F) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w => F w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun w => F w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  unfold UnforcedLeray.Cyl.curl
  exact (UnforcedLeray.Cyl.contDiff_partialQ (h1.of_le (by simp))).sub
    (UnforcedLeray.Cyl.contDiff_partialEta (h0.of_le (by simp)))

/-- **Weighted bound of the periodized unit Gaussian vorticity** (SP 2866-2867, 327-336): for
every `k, j` there is `C` with `⟨y⟩^{2k}‖D^j curl datum_d(y)‖ ≤ C` on `C_d`, uniformly in `d ≥ 1`. -/
theorem datumCurlWeighted_of (hL : DatumCurlLattice) (hC : CenteredLatticeWeighted) :
    DatumCurlWeighted := by
  unfold DatumCurlWeighted
  intro k j
  -- per-word bound, with the predicate `P w C _` of `B0147.uniform_words`
  let P : List Bool → ℝ → ℝ → Prop := fun w C _ =>
    ∀ d : ℝ, 1 ≤ d → ∀ y ∈ B0579.cell d,
      B0579.jb y ^ k * |UnforcedLeray.B0151.derivWord w
        (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤ C
  have hmono : ∀ (w : List Bool) (C b C' b' : ℝ), 0 ≤ C → P w C b → C ≤ C' → 0 < b' →
      b' ≤ b → P w C' b' := by
    intro w C b C' b' _ hP hCC _ _ d hd y hy
    exact (hP d hd y hy).trans hCC
  have hword : ∀ w : List Bool, ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧ P w C b := by
    intro w
    obtain ⟨g, hg, hdl⟩ := hL w
    obtain ⟨K, β, hK, hβ, hGB⟩ := UnforcedLeray.B0147.GP.bound hg
    obtain ⟨C, hC'⟩ := hC K β hK hβ k
    refine ⟨max C 0, 1, le_max_right _ _, one_pos, ?_⟩
    intro d hd y hy
    have hdne : d ≠ 0 := by
      have : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
      exact this.ne'
    rw [hdl d hdne]
    exact (hC' g hGB d hd y hy).trans (le_max_left _ _)
  obtain ⟨C, _, hC0, _, hS⟩ := UnforcedLeray.B0147.uniform_words P hmono hword j
  refine ⟨2 ^ j * C, fun d hd y hy => ?_⟩
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
  have hdne : d ≠ 0 := hdpos.ne'
  have hjpos : 0 < B0579.jb y := by
    unfold B0579.jb
    nlinarith [sq_nonneg y.1, sq_nonneg y.2]
  have hjk : 0 < B0579.jb y ^ k := pow_pos hjpos k
  have hW : ∀ w : List Bool, w.length = j →
      |UnforcedLeray.B0151.derivWord w (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y|
        ≤ C / B0579.jb y ^ k := by
    intro w hw
    have h := hS w hw d hd y hy
    rw [le_div_iff₀ hjk, mul_comm]
    exact h
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) :=
    dcw_contDiff_curl (UnforcedLeray.Train.datum_contDiff hdne)
  have hbr := UnforcedLeray.Short.Spine.norm_iteratedFDeriv_le_of_derivWord hsmooth j y hW
  calc B0579.jb y ^ k *
        ‖iteratedFDeriv ℝ j (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y‖
      ≤ B0579.jb y ^ k * (2 ^ j * (C / B0579.jb y ^ k)) :=
        mul_le_mul_of_nonneg_left hbr hjk.le
    _ = 2 ^ j * C := by
        field_simp

end UnforcedLeray.Short.IIIa
