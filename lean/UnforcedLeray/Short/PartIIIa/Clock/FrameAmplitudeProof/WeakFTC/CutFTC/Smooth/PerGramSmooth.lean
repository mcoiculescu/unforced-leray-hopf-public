import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PerGramSmooth.Gram

/-!
# `PartIII-a:T21/c5/1/1/2/1`: the Gram entries are `C^∞` in the cell length

Source `the November 2 reference manuscript`
lines 593-610 and 2891-2905 (the finite Gram matrix of the periodized frame; the planar dual
kernels and their fixed derivatives decay like `|y|^{-2-j}`, the growing vectors have Gaussian
tails).

**Theorem** (`perGramSmooth`): for a Part I seed kernel `κ`, every entry
`d ↦ perGram κ d i j` is `C^∞` on `Ici 1`.

**Proof.** By `perGramUnfold`, `perGram κ d i j = Σ_k T(k d)` with
`T(s) = ∫ λ_i(z₁ - s, z₂) e_j(z) dz` (translation of `gramTerm`).  Differentiating under the
integral moves the `d`-derivatives onto `λ_i`: `G_m(d) = Σ_k (-k)^m T_{∂₁^m λ_i}(k d)` satisfies
`G_m' = G_{m+1}` on `d > 1/2` (`LamJetInf.hasDerivAt_gramG`), because the all-order jet decay of
`λ_i` (`LamJetInf.good_lamP`, derived from `IsSeedKernels κ`) and the Gaussian tails of `e_j`
give `|k|^m |T_{∂₁^m λ_i}(k d)| ≲ (1 + |k|)^{-2}` uniformly on `d > 1/2`.  The tower gives `C^∞`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `gramTerm` as a cross integral `T(k d)` with the translate on `λ_i`. -/
theorem gramTerm_eq_crossT (κ : PlanarFrameKernels) (d : ℝ) (i j : Fin 2) (k : ℤ) :
    gramTerm κ d i j k = LamJetInf.crossT (κ.e j) (κ.lamP i) ((k : ℝ) * d) := by
  unfold gramTerm LamJetInf.crossT
  have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
    (fun y : ℝ × ℝ => κ.lamP i y * κ.e j (y.1 + (k : ℝ) * d, y.2)) ((k : ℝ) * d, 0)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  have h1 : z - ((k : ℝ) * d, 0) = (z.1 - (k : ℝ) * d, z.2) := by ext <;> simp
  have h2 : ((z.1 - (k : ℝ) * d, z.2).1 + (k : ℝ) * d, (z.1 - (k : ℝ) * d, z.2).2) = z := by
    ext <;> simp [sub_add_cancel]
  rw [h1, h2]

/-- **`PartIII-a:T21/c5/1/1/2/1`** (SP 593-610, 2891-2905): for a Part I seed kernel, each Gram
entry `d ↦ perGram κ d i j` is `C^∞` on `Ici 1`. -/
theorem perGramSmooth (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.PerGramSmooth κ := by
  intro hκ i j
  obtain ⟨Ce, hCe⟩ := κ.e_decay
  have hG := LamJetInf.contDiffOn_gramG_zero (κ.e_cont j) (hCe j) (LamJetInf.good_lamP hκ i)
  refine (hG.mono (Ici_subset_Ioi.2 (by norm_num))).congr fun d hd => ?_
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd
  rw [(perGramUnfold κ d hd0 i j).2]
  unfold LamJetInf.gramG LamJetInf.gramTermM
  refine tsum_congr fun k => ?_
  rw [gramTerm_eq_crossT, pow_zero, Complex.ofReal_one, one_mul, Function.iterate_zero, id]

end UnforcedLeray.Short.IIIa
