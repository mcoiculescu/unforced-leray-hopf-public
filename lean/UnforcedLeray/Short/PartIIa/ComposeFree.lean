import UnforcedLeray.Short.PartIIa.StatementsFree

/-!
# Part II-a, `free-foundation.tex`: composition

* Lemma `bg:common-body-graph` (lines 1351-1362): bijectivity is *derived* from the graph
  bound (injectivity: the bound gives `w = 0` when `(μ+L)w = 0`; the line-1409 argument) and
  the existence (surjectivity) of the semigroup-integral inverse.
* Lemma `free:weak-stress` (lines 1533-1633): uniqueness of the extension `S_μ` is derived from
  density of smooth tensors and injectivity of `μ + L` at `r = 2`.
* Numerical consequences (lines 1599-1600): the gaps `1/22`, `1/46` are computed here.
* The transported stress map (lines 1627-1632) has the same energy bounds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

theorem gammaR_two : gammaR 2 = 1 / 4 := by
  simp [gammaR]
  norm_num

/-- The body gaps `1/22` at `r = 11/4` and `1/46` at `r = 23/8` (lines 1599-1600). -/
theorem gapValues : GapValues := by
  unfold GapValues gammaR
  constructor <;> simp [ENNReal.toReal_div] <;> norm_num

/-- `μ + L` is injective on `D_r` as soon as the graph bound holds (the injectivity half of
Lemma `bg:common-body-graph`). -/
theorem bodyOp_injective_of_bound (hb : CommonBodyGraphBound) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (h1 : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (hP1 : P ≤ 1) (ν : ℝ) (hν : 0 < ν)
    (μ : ℂ) (hμ : 0 < μ.re + gammaR r) : Function.Injective (bodyOp P ν r μ) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨C, hC0, hC⟩ := hb r h1 h3
  obtain ⟨g, -, hg⟩ := hC P hP1 ν hν μ hμ w
  rw [hw, norm_zero, mul_zero] at hg
  have h0 : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ := by positivity
  have hw0 : graphNormD w ≤ 0 := by linarith
  have hn : ‖(w : Yq P r)‖ ≤ 0 := by
    have h2 := norm_nonneg (nuLapD w)
    have h3' := norm_nonneg (T0D w)
    unfold graphNormD at hw0
    linarith
  exact Subtype.ext (norm_le_zero_iff.1 hn)

/-- **Bijectivity in Lemma `bg:common-body-graph`** from the graph bound and the existence of
the semigroup-integral inverse. -/
theorem commonBodyBijective_of_parts (hb : CommonBodyGraphBound) (hs : CommonBodySurjective) :
    CommonBodyBijective := by
  intro r _ h1 h3 P _ hP1 ν hν μ hμ
  exact ⟨bodyOp_injective_of_bound hb r h1 h3 P hP1 ν hν μ hμ, hs r h1 h3 P hP1 ν hν μ hμ⟩

/-- **Lemma `bg:common-body-graph`** from its four step statements. -/
theorem commonBodyGraphLemma_of_parts (hb : CommonBodyGraphBound) (hs : CommonBodySurjective)
    (hm : CommonBodyMaximalDomain) (hp : CommonBodyProjected) (ha : CommonBodyAdjoint) :
    CommonBodyGraphLemma :=
  ⟨commonBodyBijective_of_parts hb hs, hb, hm, hp, ha⟩

/-- Uniqueness of the weak stress inverse: two bounded maps solving the smooth-tensor equation
agree (density of smooth symmetric tensors, injectivity of `μ + L` at `r = 2`). -/
theorem weakStress_ext (hbij : CommonBodyBijective) (hd : SmoothTensorsDense) {P : ℝ}
    [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {S S' : symY2 P →L[ℂ] Yq P 2} (hS : IsWeakStressInverse P ν μ S)
    (hS' : IsWeakStressInverse P ν μ S') : S = S' := by
  have hinj : Function.Injective (bodyOp P ν 2 μ) :=
    (hbij 2 ENNReal.one_lt_two (by norm_num) P hP1 ν hν μ (by rw [gammaR_two]; exact hμ)).1
  have hEq : Set.EqOn S S' {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} := by
    rintro T ⟨G, hG, hsym, hT⟩
    obtain ⟨w, hw, hwe⟩ := hS T G hG hsym hT
    obtain ⟨w', hw', hwe'⟩ := hS' T G hG hsym hT
    have hww : w = w' := hinj (hwe.trans hwe'.symm)
    rw [← hw, ← hw', hww]
  have h := Continuous.ext_on (hd P) S.continuous S'.continuous hEq
  exact ContinuousLinearMap.ext fun T => congrFun h T

/-- Existence and uniqueness of the weak stress inverse `S_μ` (line 1537, "extends uniquely"). -/
theorem weakStress_existsUnique (hbij : CommonBodyBijective) (hd : SmoothTensorsDense)
    (he : WeakStressExists) {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) :
    ∃! S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S := by
  obtain ⟨S, hS, -⟩ := he P hP1 ν hν μ hμ
  exact ⟨S, hS, fun S' hS' => weakStress_ext hbij hd hP1 hν hμ hS' hS⟩

/-- **Lemma `free:weak-stress`** from its step statements. -/
theorem weakStressLemma_of_parts (he : WeakStressExists) (hd : SmoothTensorsDense)
    (hh : WeakStressHalfDrift) (hu : WeakStressUnique) (hol : WeakStressHolomorphic) :
    WeakStressLemma :=
  ⟨he, hd, hh, hu, hol⟩

/-- **Transported stress map** (lines 1627-1632): `J_v⁻¹ S_μ J_T` has the same energy bound as
`S_μ`. -/
theorem transportedStress_norm_le {H HT : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup HT] [InnerProductSpace ℂ HT] (P : ℝ) [Fact (0 < P)]
    (Jv : H ≃ₗᵢ[ℂ] Yq P 2) (JT : HT →ₗᵢ[ℂ] symY2 P) (S : symY2 P →L[ℂ] Yq P 2) (K : ℝ)
    (hS : ∀ T : symY2 P, ‖S T‖ ≤ K * ‖T‖) (x : HT) :
    ‖TransportedStress P Jv JT S x‖ ≤ K * ‖x‖ := by
  simp only [TransportedStress, ContinuousLinearMap.comp_apply]
  calc ‖Jv.symm.toLinearIsometry.toContinuousLinearMap (S (JT.toContinuousLinearMap x))‖
      = ‖S (JT x)‖ := Jv.symm.norm_map _
    _ ≤ K * ‖JT x‖ := hS _
    _ = K * ‖x‖ := by rw [JT.norm_map]

end UnforcedLeray.Short.PartIIa
