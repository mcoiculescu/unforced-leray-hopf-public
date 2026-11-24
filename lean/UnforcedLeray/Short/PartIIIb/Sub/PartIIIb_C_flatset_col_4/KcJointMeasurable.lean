import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4

/-!
# `KcJointMeasurable` (leaf 1 of `PartIII-b:C/flatset/col/4`)

Source of record `the November 2 reference manuscript` 3426-3430.
Route: `kcLp` is `realBiotSavartKernelCLM` applied to the zero-circulation element `reX ξ`, hence
continuous in `ξ`; so `s ↦ kcLp (ξ s)` is continuous on `(0,∞)` and has a jointly strongly
measurable representative `G₁` (`exists_stronglyMeasurable_rep_of_continuousOn`).  Put
`G = 1_{s>0} G₁`; for `s ≤ 0`, `ξ s = 0` and `kcLp 0 = 0`.  Then `kcMer (ξ s) = lebRep c (G s)` for
every `s` and `lebRep_stronglyMeasurable` gives joint measurability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
  (realBiotSavartKernelCLM zeroCirculationSubmodule mem_zeroCirculationSubmodule_iff)

theorem half_lt_of_fact {m : ℝ} [Fact (1 < m)] : (1 : ℝ) / 2 < m := by
  have h : (1 : ℝ) < m := Fact.out
  linarith

theorem reX_eq_compLpL {c m : ℝ} (f : XAmb c m) :
    reX f = (Complex.reCLM : ℂ →L[ℝ] ℝ).compLpL 2 (B0579.cellMeasure c m) f := rfl

theorem continuous_reX {c m : ℝ} : Continuous (fun f : XAmb c m => reX f) := by
  have e : (fun f : XAmb c m => reX f) =
      fun f => (Complex.reCLM : ℂ →L[ℝ] ℝ).compLpL 2 (B0579.cellMeasure c m) f :=
    funext fun f => reX_eq_compLpL f
  rw [e]
  exact ((Complex.reCLM : ℂ →L[ℝ] ℝ).compLpL 2 (B0579.cellMeasure c m)).continuous

theorem reX_zero {c m : ℝ} : reX (0 : XAmb c m) = 0 := by
  rw [reX_eq_compLpL]
  exact map_zero _

/-- The zero-circulation element `reX ξ` of `X_{m,c}`. -/
def kcZ {c m : ℝ} [Fact (1 < m)] (ξ : Xmc c m) :
    zeroCirculationSubmodule (c := c) (m := m) (half_lt_of_fact (m := m)) :=
  ⟨reX ξ.1, (mem_zeroCirculationSubmodule_iff (half_lt_of_fact (m := m)) _).2 (reX_circ ξ)⟩

theorem kcLp_eq_kcZ {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :
    kcLp ξ = realBiotSavartKernelCLM (c := c) (m := m) one_le_of_fact (kcZ ξ) := rfl

theorem continuous_kcZ {c m : ℝ} [Fact (1 < m)] :
    Continuous (fun ξ : Xmc c m => kcZ ξ) :=
  Continuous.subtype_mk (continuous_reX.comp continuous_subtype_val)
    (fun ξ => (mem_zeroCirculationSubmodule_iff (half_lt_of_fact (m := m)) _).2 (reX_circ ξ))

theorem continuous_kcLp {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] :
    Continuous (fun ξ : Xmc c m => kcLp ξ) := by
  have e : (fun ξ : Xmc c m => kcLp ξ) =
      fun ξ => realBiotSavartKernelCLM (c := c) (m := m) one_le_of_fact (kcZ ξ) :=
    funext fun ξ => kcLp_eq_kcZ ξ
  rw [e]
  exact (realBiotSavartKernelCLM (c := c) (m := m) one_le_of_fact).continuous.comp
    continuous_kcZ

theorem kcLp_zero_of {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] {ξ : Xmc c m} (h : ξ = 0) :
    kcLp ξ = 0 := by
  have hz : kcZ ξ = 0 := by
    apply Subtype.ext
    rw [h]
    exact reX_zero
  rw [kcLp_eq_kcZ, hz, map_zero]

/-- A jointly strongly measurable representative of the path `s ↦ kcLp (ξ s)` for all `s`. -/
theorem kcRep {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : ℝ → Xmc c m)
    (hξ : ContinuousOn ξ (Ioi 0)) (h0 : ∀ s, s ≤ 0 → ξ s = 0) :
    ∃ G : ℝ × (ℝ × ℝ) → Merid, StronglyMeasurable G ∧
      ∀ t, (fun x => G (t, x)) =ᵐ[B0581.cellVol c] (kcLp (ξ t) : ℝ × ℝ → Merid) := by
  have hcont : ContinuousOn (fun t => kcLp (ξ t)) (Ioi 0) :=
    (continuous_kcLp (c := c) (m := m)).comp_continuousOn hξ
  obtain ⟨G₁, hG₁m, hG₁⟩ := UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
    (μ := B0581.cellVol c) (f := fun t => kcLp (ξ t)) (s := Ioi 0) measurableSet_Ioi hcont
  refine ⟨{p : ℝ × (ℝ × ℝ) | (0 : ℝ) < p.1}.indicator G₁, ?_, ?_⟩
  · exact hG₁m.indicator (measurableSet_lt measurable_const measurable_fst)
  · intro t
    by_cases ht : 0 < t
    · filter_upwards [hG₁ t ht] with x hx
      rw [Set.indicator_of_mem (show ((t, x) : ℝ × (ℝ × ℝ)) ∈
        {p : ℝ × (ℝ × ℝ) | (0 : ℝ) < p.1} from ht)]
      exact hx
    · have hz : kcLp (ξ t) = 0 := kcLp_zero_of (h0 t (not_lt.1 ht))
      rw [hz]
      filter_upwards [Lp.coeFn_zero Merid 2 (B0581.cellVol c)] with x hx
      rw [hx, Set.indicator_of_notMem (show ((t, x) : ℝ × (ℝ × ℝ)) ∉
        {p : ℝ × (ℝ × ℝ) | (0 : ℝ) < p.1} from fun h => ht h)]
      rfl

/-- **(1) Joint measurability of `K_cξ`** (source 3426-3430). -/
theorem kcJointMeasurable : KcJointMeasurable := by
  unfold KcJointMeasurable
  intro c m _ _ ξ hξ h0 i
  obtain ⟨G, hGm, hG⟩ := kcRep ξ hξ h0
  have hslice : ∀ s, kcMer (ξ s) = lebRep c (fun y => G (s, y)) :=
    fun s => (lebRep_congr (hG s)).symm
  have hΦ : Measurable fun p : ℝ × (ℝ × ℝ) => kcMer (ξ p.1) p.2 := by
    have hs : StronglyMeasurable fun p : ℝ × (ℝ × ℝ) => lebRep c (fun y => G (p.1, y)) p.2 :=
      lebRep_stronglyMeasurable hGm
    have e : (fun p : ℝ × (ℝ × ℝ) => kcMer (ξ p.1) p.2) =
        fun p => lebRep c (fun y => G (p.1, y)) p.2 := by
      funext p
      rw [hslice p.1]
    rw [e]
    exact hs.measurable
  have hcoord : Measurable fun v : Merid => ((v i : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      ((EuclideanSpace.proj i : Merid →L[ℝ] ℝ).continuous.measurable)
  exact hcoord.comp hΦ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
