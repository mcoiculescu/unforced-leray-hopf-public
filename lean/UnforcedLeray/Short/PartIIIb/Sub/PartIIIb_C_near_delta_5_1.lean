import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_5
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# `PartIII-b:C/near/delta/5/1`: `StreamCompletionDecay` from three train leaves (source 2703-2729)

Source `the November 2 reference manuscript`
lines 2703-2729: the mean stream and its fixed weighted derivatives have size `(1+s)^{-1/2}` on the
transverse scale `√(1+s)` (`PartI.TrainMeanExpansion`, `p = ∞`), the fluctuation decays
exponentially (`PartI.TrainFluctuationDecay`), so the stream completion
`H = (1-η∂_η-2s∂_s)ψ` has `√s W |H| ≤ P_ν`.  Leaves are stated for a train at `(ν, c)`,
`c = (ν²)⁻¹` (`= PartI.trainPeriod 2 ν`), to avoid casts on `B0140.TrainSol`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03

/-- **Leaf 1 (mean stream, source 2703-2723, 2724-2729)**: for `m_Z > 3/2` there are `C, N, ν₀`
with `√s W |(1-η∂_η-2s∂_s) S| ≤ C(1+c+ν⁻¹)^N` for the mean stream `S(s,η) = \bar ψ`.  From
`PartI.TrainMeanExpansion` at `p = ∞`, `m = ⌈m_Z⌉`, `b ∈ {0,1}`, `ℓ ∈ {0,1}`: the bound
`|η|^m |∂_η^b ∂_s^ℓ S| ≤ P (1+s)^{(m-b-1)/2-ℓ}` and `W ≤ ⟨η⟩^{m_Z}(1+s)^{-m_Z/2}·const`. -/
def StreamMeanCompletion : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ q η : ℝ,
        Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
          |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream tr r z.2) s q η|
          ≤ UnforcedLeray.Short.PartI.polyP C N ν c

/-- **Leaf 2 (fluctuation, source 2703-2723)**: the same bound for the fluctuation
`\tilde ψ = ψ - \bar ψ`, from `PartI.TrainFluctuationDecay` (`m = ⌈m_Z⌉`, `(ℓ,j) ∈ {(0,0),(0,1),
(1,0)}`, `wSupNorm`, `IIIa.T23Tail.abs_raisedStream_le`-type three-term bound) and the polynomial
bound of `√s s^ℓ e^{-κνs/c²}` in `ν⁻¹`. -/
def StreamFluctCompletion : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ q η : ℝ,
        Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
          |raisedStream (fun r z => tr.ψ r z - UnforcedLeray.Short.PartI.hmean c (tr.ψ r) z.2)
            s q η| ≤ UnforcedLeray.Short.PartI.polyP C N ν c

/-- **Leaf 3 (linearity of the completion on `ψ = \bar ψ + \tilde ψ`)**: for a BUC train the stream
is differentiable in `(s,η)` for `s > 0` and so is its horizontal mean (`sct:heat`, smoothness of the
mean stream, lines 397-402), hence `raisedStream` splits. -/
def RaisedStreamSplit : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < ν → 0 < c →
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ q η : ℝ,
      raisedStream tr.ψ s q η =
        raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream tr r z.2) s q η +
        raisedStream (fun r z => tr.ψ r z - UnforcedLeray.Short.PartI.hmean c (tr.ψ r) z.2) s q η

theorem polyP_le_inv_pow (C : ℝ) (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ ≤ |C| * 3 ^ N * (ν⁻¹) ^ (2 * N) := by
  unfold UnforcedLeray.Short.PartI.polyP
  have h1 : (1 : ℝ) ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have h2 : (ν ^ 2)⁻¹ = (ν⁻¹) ^ 2 := by rw [inv_pow]
  have h3 : 1 + (ν ^ 2)⁻¹ + ν⁻¹ ≤ 3 * (ν⁻¹) ^ 2 := by
    rw [h2]; nlinarith
  have h4 : (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ N ≤ (3 * (ν⁻¹) ^ 2) ^ N :=
    pow_le_pow_left₀ (by positivity) h3 N
  calc C * (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ N ≤ |C| * (1 + (ν ^ 2)⁻¹ + ν⁻¹) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (3 * (ν⁻¹) ^ 2) ^ N := mul_le_mul_of_nonneg_left h4 (abs_nonneg C)
    _ = |C| * 3 ^ N * (ν⁻¹) ^ (2 * N) := by rw [mul_pow, ← pow_mul]; ring

/-- `StreamCompletionDecay` from the three leaves. -/
theorem streamCompletionDecay_of (h1 : StreamMeanCompletion) (h2 : StreamFluctCompletion)
    (h3 : RaisedStreamSplit) : StreamCompletionDecay := by
  intro dm dp hdm mZ hmZ
  obtain ⟨C1, N1, a1, ha1, e1⟩ := h1 mZ hmZ
  obtain ⟨C2, N2, a2, ha2, e2⟩ := h2 mZ hmZ
  refine ⟨|C1| * 3 ^ N1 + |C2| * 3 ^ N2, 2 * (N1 + N2), min 1 (min a1 a2),
    lt_min one_pos (lt_min ha1 ha2), ?_⟩
  intro p d hreg hν pt hpt
  have hνp := p.ν_pos
  have hνa1 : p.ν ≤ a1 := le_trans hν ((min_le_right _ _).trans (min_le_left _ _))
  have hνa2 : p.ν ≤ a2 := le_trans hν ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := le_trans hν (min_le_left _ _)
  obtain ⟨s, q, η⟩ := pt
  have hc : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hbuc := hreg.train_buc
  have hW : 0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) := by
    unfold UnforcedLeray.Short.IIIa.transWeight; positivity
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hspl := h3 p.ν p.c p.train hνp p.c_pos hbuc s hpt q η
  have b1 := e1 p.ν p.c p.train hνp hνa1 hc hbuc s hpt q η
  have b2 := e2 p.ν p.c p.train hνp hνa2 hc hbuc s hpt q η
  have hP1 := polyP_le_inv_pow C1 N1 p.ν hνp hν1
  have hP2 := polyP_le_inv_pow C2 N2 p.ν hνp hν1
  rw [← hc] at hP1 hP2
  have hi : (1 : ℝ) ≤ p.ν⁻¹ := one_le_inv_iff₀.2 ⟨hνp, hν1⟩
  have m1 : (p.ν⁻¹) ^ (2 * N1) ≤ (p.ν⁻¹) ^ (2 * (N1 + N2)) :=
    pow_le_pow_right₀ hi (by omega)
  have m2 : (p.ν⁻¹) ^ (2 * N2) ≤ (p.ν⁻¹) ^ (2 * (N1 + N2)) :=
    pow_le_pow_right₀ hi (by omega)
  have hw : 0 ≤ Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) :=
    mul_nonneg hsq hW
  show Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) * _ ≤ _
  rw [hspl]
  calc Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
        |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream p.train r z.2) s q η +
          raisedStream (fun r z => p.train.ψ r z -
            UnforcedLeray.Short.PartI.hmean p.c (p.train.ψ r) z.2) s q η|
      ≤ Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
        (|raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream p.train r z.2) s q η| +
          |raisedStream (fun r z => p.train.ψ r z -
            UnforcedLeray.Short.PartI.hmean p.c (p.train.ψ r) z.2) s q η|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ = Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
          |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream p.train r z.2) s q η| +
        Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
          |raisedStream (fun r z => p.train.ψ r z -
            UnforcedLeray.Short.PartI.hmean p.c (p.train.ψ r) z.2) s q η| := by ring
    _ ≤ (|C1| * 3 ^ N1 * (p.ν⁻¹) ^ (2 * (N1 + N2))) +
        (|C2| * 3 ^ N2 * (p.ν⁻¹) ^ (2 * (N1 + N2))) := by
        have a : |C1| * 3 ^ N1 * (p.ν⁻¹) ^ (2 * N1) ≤ |C1| * 3 ^ N1 * (p.ν⁻¹) ^ (2 * (N1 + N2)) :=
          mul_le_mul_of_nonneg_left m1 (by positivity)
        have b : |C2| * 3 ^ N2 * (p.ν⁻¹) ^ (2 * N2) ≤ |C2| * 3 ^ N2 * (p.ν⁻¹) ^ (2 * (N1 + N2)) :=
          mul_le_mul_of_nonneg_left m2 (by positivity)
        linarith
    _ = (|C1| * 3 ^ N1 + |C2| * 3 ^ N2) * p.ν⁻¹ ^ (2 * (N1 + N2)) := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
