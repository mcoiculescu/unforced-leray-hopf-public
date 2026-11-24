import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Units.B0414.PhaseOrthogonal

/-!
# Part II-a, task `PartII-a:F16`: the half-drift bound, reduced to four leaf lemmas

Source `the November 2 reference manuscript`
lines 1585-1598.  With `R = R_μ = (μ+L)^{-1}𝐏` (bounded on `Y_2`), `C = 1 + |B|`, `D = 1 + A`:
the direct graph bound for `B R` and the adjoint graph bound for `A R^*` (lines 1585-1587) give,
by the three-lines argument (`FreeStress.free_stress_28_Y2'`), a bounded `S₀` with
`C^{1/2} R D^{1/2} x = S₀ x`; the tensor divergence is `𝐏 div T = D^{1/2} X T` with `X` bounded by
`C_Q ν^{-1/2}` (lines 1596-1598); on smooth symmetric tensors `S_μ T = R 𝐏 div T`; and the
general `T` follows by density of smooth tensors and closedness of `C^{1/2}`.

Everything but the four leaf Props (`BodyInverseBounded`, `BodyDirectGraph`, `BodyAdjointGraph`,
`TensorDivRiesz`) and the existing `CommonBodyBijective`, `SmoothTensorsDense` is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology SchwartzMap
open scoped ENNReal NNReal Laplacian

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- `R` is the body inverse `(μ+L)^{-1}𝐏` on `Y_2` (source 1363-1368, 1553): for every `f`,
`R f ∈ D_2` solves `(μ+L)(R f) = 𝐏 f`. -/
def IsBodyInverse (P ν : ℝ) [Fact (0 < P)] (μ : ℂ) (R : Yq P 2 →L[ℂ] Yq P 2) : Prop :=
  ∀ f : Yq P 2, ∃ w : D P ν 2, (w : Yq P 2) = R f ∧
    bodyOp P ν 2 μ w = lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f

/-- Direct graph bound: `B R v` exists as the derivative at `t = 0` of `e^{tB} R v`
(phase translation composed with the `L²`-normalised dilation), `‖B R v‖ ≤ M ‖v‖`. -/
def DirectGraphBound (P : ℝ) [Fact (0 < P)] (R : Yq P 2 →L[ℂ] Yq P 2) (M : ℝ) : Prop :=
  ∀ v : Yq P 2, ∃ w : Yq P 2,
    Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ • (FreeStress.phaseDilation P t (R v) - R v)) (𝓝[≠] 0) (𝓝 w) ∧
      ‖w‖ ≤ M * ‖v‖

/-- Adjoint graph bound: `A R^* v = -νΔ R^* v` (fibrewise in `𝓢'(ℝ³;ℂ³)`, a.e. phase) lies in
`Y_2` with norm `≤ M ‖v‖`. -/
def AdjointGraphBoundY (P ν : ℝ) [Fact (0 < P)] (R : Yq P 2 →L[ℂ] Yq P 2) (M : ℝ) : Prop :=
  ∀ v : Yq P 2, ∃ w : Yq P 2, (∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      (-(ν : ℂ)) • Δ (((((ContinuousLinearMap.adjoint R) v : Yq P 2) τ :
        Lp CVec3 2 (volume : Measure Space))) : 𝓢'(Space, CVec3)) =
        (((w : Yq P 2) τ : Lp CVec3 2 (volume : Measure Space)) : 𝓢'(Space, CVec3))) ∧
    ‖w‖ ≤ M * ‖v‖

/-- **Leaf 1** (source 1553-1554, 1585-1586; `bg:common-body-graph` at `r = 2`): the body inverse
`R_μ` exists as a bounded operator of `Y_2`, with norm bounded uniformly in `P ≤ 1`, `ν > 0` and
`μ` in a compact subset of `Re μ > -1/4`.  (`‖w‖ ≤ ‖w‖_{D_2} ≤ C(1+(1+|μ|)/a)‖𝐏f‖`.) -/
def BodyInverseBounded : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, 0 < μ.re + 1 / 4) → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K,
      ∃ R : Yq P 2 →L[ℂ] Yq P 2, IsBodyInverse P ν μ R ∧ ‖R‖ ≤ C

/-- **Leaf 2** (source 1585-1586: "direct graph bounds `C R_μ`", `bg:common-body-graph` at `r = 2`
with `B = 𝒯 - 3/4`): `B R_μ` is bounded with a constant uniform in `P ≤ 1`, `ν > 0`, `μ ∈ K`. -/
def BodyDirectGraph : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, 0 < μ.re + 1 / 4) → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K,
      ∀ R : Yq P 2 →L[ℂ] Yq P 2, IsBodyInverse P ν μ R → DirectGraphBound P R M

/-- **Leaf 3** (source 1586-1587: "the actual adjoint graph bounds `D R_μ^*`", `CommonBodyAdjoint`
and duality `R^* v` = the distributional solution of the adjoint equation): `A R_μ^*` is bounded
uniformly in `P ≤ 1`, `ν > 0`, `μ ∈ K`. -/
def BodyAdjointGraph : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, 0 < μ.re + 1 / 4) → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K,
      ∀ R : Yq P 2 →L[ℂ] Yq P 2, IsBodyInverse P ν μ R → AdjointGraphBoundY P ν R M

/-- **Leaf 4** (source 1596-1598): `div = ν^{-1/2} A^{1/2} 𝒬` with `𝒬` a bounded Riesz combination
(spatial Fourier transform), `D^{-1/2} A^{1/2}` bounded and Leray commuting with `A`: there is a
bounded `X : Y_2(Sym_3) → Y_2` of norm `≤ C_Q ν^{-1/2}` (`C_Q` independent of `P ≤ 1`, `ν`) with
`D^{1/2} X T = 𝐏 div G` for every smooth symmetric phase tensor `G` representing `T`. -/
def TensorDivRiesz : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ (ν : ℝ) (hν : 0 < ν),
    ∃ X : symY2 P →L[ℂ] Yq P 2, ‖X‖ ≤ C * ν ^ (-(1 / 2 : ℝ)) ∧
      ∀ (T : symY2 P) (G : Fin 3 → ℝ × Space → CVec3), (∀ i, IsPhaseTest P (G i)) →
        IsSymRows G → smoothTensor P G = (T : Y2Sym P) →
          (FreeStress.phaseD0 P ν hν.le).HasPow (1 / 2) (X T)
            (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G)))

theorem gammaR_two : gammaR 2 = 1 / 4 := by
  unfold gammaR
  norm_num

/-- **The half-drift bound** from the four leaves. -/
theorem weakStressHalfDrift_of (hbij : CommonBodyBijective) (hdense : SmoothTensorsDense)
    (h1 : BodyInverseBounded) (h2 : BodyDirectGraph) (h3 : BodyAdjointGraph)
    (h4 : TensorDivRiesz) : WeakStressHalfDrift := by
  intro K hK hKpos
  obtain ⟨CR, hCR0, hR⟩ := h1 K hK hKpos
  obtain ⟨MB, hMB0, hB⟩ := h2 K hK hKpos
  obtain ⟨MA, hMA0, hA⟩ := h3 K hK hKpos
  obtain ⟨CQ, hCQ0, hQ⟩ := h4
  refine ⟨Real.sqrt ((CR + MA) * (CR + MB)) * CQ, by positivity, ?_⟩
  intro P _ hP ν hν μ hμ S hS T
  obtain ⟨R, hRinv, hRn⟩ := hR P hP ν hν μ hμ
  obtain ⟨X, hXn, hXG⟩ := hQ P hP ν hν
  obtain ⟨S0, hS0n, hS0⟩ := FreeStress.free_stress_28_Y2' P ν hν.le R hMA0 hMB0
    (hB P hP ν hν μ hμ R hRinv) (hA P hP ν hν μ hμ R hRinv)
  have hS0n' : ‖S0‖ ≤ Real.sqrt ((CR + MA) * (CR + MB)) := by
    refine hS0n.trans (Real.sqrt_le_sqrt ?_)
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  -- smooth approximants
  have hmem : T ∈ closure {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} := by
    rw [(hdense P).closure_eq]; exact mem_univ _
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.1 hmem
  have hμpos : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hKpos μ hμ
  have hinj := (hbij 2 ENNReal.one_lt_two (by norm_num) P hP ν hν μ hμpos).1
  have hn : ∀ n, (FreeStress.phaseC0 P).HasPow (1 / 2) (S (u n)) (S0 (X (u n))) := by
    intro n
    obtain ⟨G, hG1, hG2, hG3⟩ := hu n
    set f := testElem P 2 (tensorDiv G) with hf
    set y := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f with hy
    have hp := hXG (u n) G hG1 hG2 hG3
    obtain ⟨w, hw1, hw2⟩ := hS (u n) G hG1 hG2 hG3
    obtain ⟨w', hw1', hw2'⟩ := hRinv y
    have hyfix : lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top y = y :=
      (B0414.lerayY_two_eq_self_iff y).2 (B0414.lerayY_two_mem f)
    have hww : w = w' := hinj (by rw [hw2, hw2', hyfix])
    have hSR : S (u n) = R y := by rw [← hw1, ← hw1', hww]
    rw [hSR]
    exact hS0 _ _ hp
  have hlim := FreeStress.MulRep.HasPow.of_tendsto (T := FreeStress.phaseC0 P) (s := 1 / 2)
    (by norm_num) (xn := fun n => S (u n)) (yn := fun n => S0 (X (u n)))
    ((S.continuous.tendsto T).comp hut) (((S0.comp X).continuous.tendsto T).comp hut) hn
  refine ⟨S0 (X T), hlim, ?_⟩
  have hT : ‖T‖ = ‖(T : Y2Sym P)‖ := rfl
  calc ‖S0 (X T)‖ ≤ ‖S0‖ * ‖X T‖ := S0.le_opNorm _
    _ ≤ ‖S0‖ * (‖X‖ * ‖T‖) := by
        gcongr; exact X.le_opNorm _
    _ ≤ Real.sqrt ((CR + MA) * (CR + MB)) * ((CQ * ν ^ (-(1 / 2 : ℝ))) * ‖T‖) := by
        gcongr
    _ = Real.sqrt ((CR + MA) * (CR + MB)) * CQ * ν ^ (-(1 / 2 : ℝ)) * ‖(T : Y2Sym P)‖ := by
        rw [hT]; ring

end UnforcedLeray.Short.PartIIa
