import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIa.Compose
import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge

/-!
# Sub-lemma for `PartIII-b:C/near/delta/5` (`RawStreamCompletion`, source 2724-2729)

`StreamCompletionDecay` is the content of the source sentence "The stream completion
`ε(1-η∂_η-2s∂_s)ψ` has size `P_ν ε(1+s)^{-1/2}`" (2724-2729) in the weighted form
`√s W |H| ≤ P_ν` for the stream completion `H = raisedStream ψ`; `rawStreamCompletion_of` derives
`RawStreamCompletion` from it (chart identity `IIIa.chartCoeff_raw`, `trainMer_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- **Weighted size of the stream completion** (source 2724-2729, from the train heat expansion
2703-2723: mean stream and fixed weighted derivatives of size `(1+s)^{-1/2}` on transverse scale
`√(1+s)`; fluctuation decay; early smoothness): for `m_Z > 3/2` there are `C, k, ν₀` with
`√s W |(1 - η∂_η - 2s∂_s)ψ(s,q,η)| ≤ C ν^{-k}` for every `s > 0`, `(q, η)`, at every level of the
regime with `ν ≤ ν₀` (`c = ν⁻²`). -/
def StreamCompletionDecay : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ pt : Chart, 0 < pt.1 →
        Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
          |UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2| ≤ C * p.ν⁻¹ ^ k

theorem rawStreamCompletion_of (h : StreamCompletionDecay) : RawStreamCompletion := by
  intro dm dp hdm mZ hmZ
  obtain ⟨C, k, ν₀, hν₀, hC⟩ := h dm dp hdm mZ hmZ
  refine ⟨C, k, ν₀, hν₀, ?_⟩
  intro p d hreg hν pt hpt
  have hε := p.ε_pos
  have hdiff : UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt =
      (p.ε * UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    rw [UnforcedLeray.Short.IIIa.chartCoeff_raw p hpt, trainMer_eq p.trainData pt hpt.le]
    unfold UnforcedLeray.Cons.C03.rawProfile
    exact add_sub_cancel_left _ _
  have hn : ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ =
      p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2| := by
    rw [hdiff, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_mul, abs_of_pos hε]
  rw [hn]
  have h1 := hC p d hreg hν pt hpt
  calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        (p.ε * |UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2|)
      = p.ε * (Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        |UnforcedLeray.Cons.C03.raisedStream p.train.ψ pt.1 pt.2.1 pt.2.2|) := by ring
    _ ≤ p.ε * (C * p.ν⁻¹ ^ k) := mul_le_mul_of_nonneg_left h1 hε.le
    _ = C * p.ν⁻¹ ^ k * p.ε := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
