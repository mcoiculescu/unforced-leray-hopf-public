import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipZeroCirc

/-!
# `PartIII-a:T21/2/3/1/9` (`ladTransposition`), decomposition

Source: `the November 2 reference manuscript` (SP) lines 3052-3058, 3074-3075,
3230-3240.  `LadTransposition m` follows from the closed theorems `adjWeakPointwise`,
`adjWeakChiBound`, `ladFlowZeroCirc` and two leaves: the density lemma `LadTranspApprox`
(approximation of the zero-circulation `X_m` datum by real cylinder tests, with convergent kernel
velocities) and the limit passage `LadTranspLimit`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- **Leaf A** (density, SP 3230-3240: `‖K_c f‖₂ ≤ C‖f‖_{X_m}` for zero circulation, mollified and
cut-off cylinder tests with a fixed bump correcting the circulation): a zero-circulation
`w ∈ X_{m,c}` with Biot-Savart velocity `u` is the `X_{m,c}`-limit of `a_n + i b_n`, `a_n, b_n`
real cylinder tests with kernel velocities `ua_n, ub_n`, and the velocities converge to `u`
in `L²(cell)`. -/
def LadTranspApprox (m : ℝ) : Prop :=
  ∀ (c : ℝ) (w : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ), 1 ≤ c →
    MemLp w 2 (B0579.cellMeasure c m) → HasZeroCirculation c w → IsBiotSavart c w u →
    ∃ (a b : ℕ → ℝ × ℝ → ℝ) (ua ub : ℕ → ℝ × ℝ → Fin 2 → ℝ),
      (∀ n, B0579.IsCylTest c (a n) ∧ B0579.IsCylTest c (b n) ∧
        IsKernelBiotSavart c (a n) (ua n) ∧ IsKernelBiotSavart c (b n) (ub n)) ∧
      Tendsto (fun n => xNorm c m
        (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x)) atTop (𝓝 0) ∧
      ∀ j : Fin 2, Tendsto (fun n => eLpNorm
        (fun x => ((ua n x j : ℝ) : ℂ) + Complex.I * ((ub n x j : ℝ) : ℂ) - u x j) 2
          (volume.restrict (B0579.cell c))) atTop (𝓝 0)

/-- **Leaf B** (limit passage, SP 3052-3058): if the pointwise adjoint identity holds for
real cylinder tests `a_n, b_n` (with kernel velocities `ua_n, ub_n`) and
`a_n + i b_n → w ρ` in `X_m`, the velocities converge to `u ρ` in `L²`, then
`∫ w ρ χ = ∫ (u ρ·∇E) φ ρ`.  Left side: `χ ∈ X_{-m}` and the `X_m`/`X_{-m}` Cauchy-Schwarz
(in particular `χ a_n`, `χ b_n`, `χ w ρ` are integrable); right side: `φ ρ ∇E ∈ L²(cell)` since
`φ ρ ∈ X_{-m}` (`IsAdjointFlow.memX`) and `LadTrainBdd` (`jb^{(m+2)/2}|∇E| ≤ C`, `jb ≥ 1`). -/
def LadTranspLimit (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (w : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ),
    0 < ν → 1 ≤ c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ → ρ ∈ Ioo t s →
    MemLp w 2 (B0579.cellMeasure c m) → IsBiotSavart c w u →
    MemLp (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) →
    ∀ (a b : ℕ → ℝ × ℝ → ℝ) (ua ub : ℕ → ℝ × ℝ → Fin 2 → ℝ),
      (∀ n, B0579.IsCylTest c (a n) ∧ B0579.IsCylTest c (b n)) →
      (∀ n, ∫ x in B0579.cell c, ladChi tr φ ρ x * ((a n x : ℝ) : ℂ) =
        ∫ x in B0579.cell c, φ ρ x *
          ((ua n x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
            ua n x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) →
      (∀ n, ∫ x in B0579.cell c, ladChi tr φ ρ x * ((b n x : ℝ) : ℂ) =
        ∫ x in B0579.cell c, φ ρ x *
          ((ub n x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
            ub n x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) →
      Tendsto (fun n => xNorm c m
        (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x)) atTop (𝓝 0) →
      (∀ j : Fin 2, Tendsto (fun n => eLpNorm
        (fun x => ((ua n x j : ℝ) : ℂ) + Complex.I * ((ub n x j : ℝ) : ℂ) - u x j) 2
          (volume.restrict (B0579.cell c))) atTop (𝓝 0)) →
      ∫ x in B0579.cell c, w x * ladChi tr φ ρ x =
        ∫ x in B0579.cell c, ladForce tr u ρ x * φ ρ x

theorem ladTransposition_of (m : ℝ) (hm : 8 < m) (hA : LadTranspApprox m)
    (hL : LadTranspLimit m) : LadTransposition m := by
  intro ν c tr t s g φ f w u hν hc ht hts hB hφ hf hf0 hflow ρ hρ
  have hz : HasZeroCirculation c (w ρ) :=
    ladFlowZeroCirc m (by linarith) ν c tr t f w u hc hf0 hflow ρ hρ.1.le
  have hmem := hflow.memX ρ hρ.1.le
  have hbs := hflow.biotSavart ρ hρ.1.le
  obtain ⟨a, b, ua, ub, hT, hX, hV⟩ := hA c (w ρ) (u ρ) hc hmem hz hbs
  obtain ⟨M, hM⟩ := ladChiBound_of_weak m (adjWeakChiBound m hm) ν c tr t s g φ hν hc ht hts hB hφ
  have hP := ladAdjPointwise_of_weak m (adjWeakPointwise m)
  refine hL ν c tr t s g φ (w ρ) (u ρ) ρ hν hc ht hts hB hφ hρ hmem hbs (hM ρ hρ).1 a b ua ub
    (fun n => ⟨(hT n).1, (hT n).2.1⟩) ?_ ?_ hX hV
  · intro n
    exact hP ν c tr t s g φ hν (by linarith) ht hts hB hφ ρ hρ (a n) (ua n) (hT n).1
      (hT n).2.2.1
  · intro n
    exact hP ν c tr t s g φ hν (by linarith) ht hts hB hφ ρ hρ (b n) (ub n) (hT n).2.1
      (hT n).2.2.2

end UnforcedLeray.Short.IIIa
