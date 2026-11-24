import UnforcedLeray.Units.B0221.Conjugation

/-!
# B0221 helper: the scalar unitary lift and conjugated operators

Blueprint unit B0221 (label `eq:st18-t00114`), `paper/main.tex` lines 3316–3346; infrastructure
INF24 (unbounded operator domains transported by a unitary).

B0220 builds the rescaled lift `J_ε` of meridional (vector) profiles. The scalar generator
`A_ε` acts on scalar profiles, so this file builds the scalar lift
`J_ε b = (√(2π) ε)⁻¹ a b(s,q,η)` (`Jsc`, the same weighted composition `B0220.WeightedComp`
with the same constant `B0220.jConst`) and proves that it is unitary from
`H = L²(s^{-3/2} ds dq dη)` onto the axisymmetric scalar fields of `L²(dx dτ)` (`range_Jsc`,
`JscEquiv`). The proof of `range_Jsc` adapts `B0220.range_J`.

`conjOp G` is the conjugate `J_ε⁻¹ G J_ε` of an operator `G` on `L²(dx dτ)`, defined by its
graph `{(b, b') | (J_ε b, J_ε b') ∈ graph G}` (Mathlib `LinearPMap`). No condition is added at
the axis or at an age endpoint: the domain is exactly the preimage
(`mem_domain_conjOp_iff`, `mem_domain_conjOp_iff_of_preserves`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal
open UnforcedLeray.B0220

namespace UnforcedLeray.B0221

/-- `L²(dx dτ)` of scalar fields over one `τ` period `(0, 2εc]`. -/
abbrev PhysL2sc (ε c : ℝ) := Lp ℝ 2 (physMeasure ε c)

/-! ### The scalar lift `J_ε` -/

/-- `J_ε` on scalar profiles as a weighted composition: `b ↦ (√(2π) ε)⁻¹ a b(s,q,η)`. -/
def jCompSc {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    WeightedComp (physMeasure ε c) (measureH c) ℝ ℝ where
  T := cellChart ε c
  L y := (jConst ε * liftA y.1) • LinearMap.id
  ρ y := jConst ε * liftA y.1
  measurable_T := measurable_cellChart ε c
  measurable_ρ := (measurable_liftA.comp measurable_fst).const_mul _
  measurable_L := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    exact (((measurable_liftA.comp measurable_fst).const_mul _).comp measurable_fst).mul
      measurable_snd
  nonneg_ρ y := mul_nonneg (jConst_nonneg hε) (liftA_nonneg _)
  norm_L y v := by
    rw [LinearMap.smul_apply, LinearMap.id_apply, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (jConst_nonneg hε) (liftA_nonneg _))]
  map_eq := map_cellChart_jDensity hε hc

/-- The scalar rescaled lift `J_ε : H → L²(dx dτ)`, an isometry (tex lines 3309–3311 for the
scalar lift `U = a b` of `eq:st18-t00113`). -/
def Jsc {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : HSpace c ℝ →ₗᵢ[ℝ] PhysL2sc ε c :=
  (jCompSc hε hc).toLI

/-- `J_ε b = (√(2π) ε)⁻¹ U`, `U = a b(s,q,η)` the lift of the periodic extension of `b`. -/
theorem coeFn_Jsc {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c ℝ) :
    Jsc hε hc b =ᵐ[physMeasure ε c] fun y => jConst ε * liftU ε (periodize c b) y := by
  filter_upwards [(jCompSc hε hc).coeFn_toLI b] with y hy
  rw [Jsc, hy]
  simp only [WeightedComp.compFun, jCompSc, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, liftU]
  rw [mul_assoc]
  rfl

/-- The axisymmetric scalar fields `V(x, τ) = B(r, z, τ)` of `L²(dx dτ)`. -/
def axisymSubspace (ε c : ℝ) : Submodule ℝ (PhysL2sc ε c) where
  carrier := {V | ∃ B : ℝ × ℝ × ℝ → ℝ, Measurable B ∧
    (V : Space × ℝ → ℝ) =ᵐ[physMeasure ε c] fun y => B (radius y.1, y.1 2, y.2)}
  add_mem' := by
    rintro V W ⟨B, hB, hV⟩ ⟨C, hC, hW⟩
    refine ⟨B + C, hB.add hC, ?_⟩
    filter_upwards [Lp.coeFn_add V W, hV, hW] with y h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.add_apply]
  zero_mem' := ⟨0, measurable_const, by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := physMeasure ε c)] with y hy
    rw [hy]
    simp⟩
  smul_mem' := by
    rintro r V ⟨B, hB, hV⟩
    refine ⟨r • B, hB.const_smul r, ?_⟩
    filter_upwards [Lp.coeFn_smul r V, hV] with y h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply]

/-- `J_ε` maps `H` onto the axisymmetric scalar fields (adapted from `B0220.range_J`). -/
theorem range_Jsc {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    LinearMap.range (Jsc hε hc).toLinearMap = axisymSubspace ε c := by
  ext V
  constructor
  · rintro ⟨b, rfl⟩
    have hbm : Measurable (b : Profile → ℝ) := (Lp.stronglyMeasurable b).measurable
    refine ⟨fun w => (jConst ε * w.1⁻¹) *
      b ((w.1 ^ 2)⁻¹, reduceIoc c (ε⁻¹ * Real.log w.1 + w.2.2 / (2 * ε)), w.2.1 / (ε * w.1)),
      ?_, ?_⟩
    · refine (measurable_fst.inv.const_mul _).mul (hbm.comp ?_)
      exact ((measurable_fst.pow_const 2).inv).prodMk
        (((measurable_reduceIoc c).comp
          (((Real.measurable_log.comp measurable_fst).const_mul _).add
            ((measurable_snd.comp measurable_snd).div_const _))).prodMk
          ((measurable_fst.comp measurable_snd).div (measurable_fst.const_mul ε)))
    · filter_upwards [(jCompSc hε hc).coeFn_toLI b] with y hy
      change (jCompSc hε hc).toLI b y = _
      rw [hy]
      simp only [WeightedComp.compFun, jCompSc, LinearMap.smul_apply, LinearMap.id_apply,
        smul_eq_mul]
      rfl
  · rintro ⟨B, hB, hV⟩
    set b₀ : Profile → ℝ := fun p =>
      (√(2 * π) * ε * invR p) * B (invR p, invZ ε p, invTau ε c p) with hb₀
    have hb₀m : Measurable b₀ :=
      (measurable_invR.const_mul _).mul
        (hB.comp (measurable_invR.prodMk ((measurable_invZ ε).prodMk (measurable_invTau ε c))))
    have hpt : (jCompSc hε hc).compFun b₀ =ᵐ[physMeasure ε c]
        fun y => B (radius y.1, y.1 2, y.2) := by
      filter_upwards [ae_physMeasure ε c] with y ⟨hr, hτ⟩
      obtain ⟨h1, h2, h3⟩ := invChart hε hc hr hτ
      have hk : √(2 * π) * ε * radius y.1 * (jConst ε * liftA y.1) = 1 := by
        have : √(2 * π) ≠ 0 := by positivity
        simp only [jConst, liftA]
        field_simp
      simp only [WeightedComp.compFun, jCompSc, LinearMap.smul_apply, LinearMap.id_apply,
        smul_eq_mul, hb₀, h1, h2, h3]
      rw [← mul_assoc, mul_comm (jConst ε * liftA y.1), hk, one_mul]
    have hb₀L : MemLp b₀ 2 (measureH c) :=
      ⟨hb₀m.aestronglyMeasurable, by
        rw [← (jCompSc hε hc).eLpNorm_compFun hb₀m, eLpNorm_congr_ae (hpt.trans hV.symm)]
        exact Lp.eLpNorm_lt_top V⟩
    refine ⟨hb₀L.toLp b₀, Lp.ext ?_⟩
    exact ((jCompSc hε hc).coeFn_toLI_toLp hb₀L).trans (hpt.trans hV.symm)

/-- `J_ε` is unitary from scalar `H` onto the axisymmetric scalar fields of `L²(dx dτ)`. -/
def JscEquiv {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : HSpace c ℝ ≃ₗᵢ[ℝ] axisymSubspace ε c :=
  (Jsc hε hc).equivRange.trans (LinearIsometryEquiv.ofEq _ _ (range_Jsc hε hc))

theorem JscEquiv_apply {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c ℝ) :
    (JscEquiv hε hc b : PhysL2sc ε c) = Jsc hε hc b := rfl

/-! ### Conjugation of an operator by `J_ε` (INF24) -/

section Conj

variable {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)

/-- The graph `{(b, b') | (J_ε b, J_ε b') ∈ graph G}` of the conjugate. -/
def conjGraph (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) : Submodule ℝ (HSpace c ℝ × HSpace c ℝ) :=
  G.graph.comap ((Jsc hε hc).toLinearMap.prodMap (Jsc hε hc).toLinearMap)

theorem mem_conjGraph (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) (b b' : HSpace c ℝ) :
    (b, b') ∈ conjGraph hε hc G ↔ (Jsc hε hc b, Jsc hε hc b') ∈ G.graph := Iff.rfl

theorem conjGraph_functional (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) :
    ∀ (x : HSpace c ℝ × HSpace c ℝ) (_ : x ∈ conjGraph hε hc G) (_ : x.1 = 0), x.2 = 0 := by
  rintro ⟨b, b'⟩ hx h0
  simp only at h0
  subst h0
  have hx' : (Jsc hε hc 0, Jsc hε hc b') ∈ G.graph := hx
  rw [map_zero] at hx'
  have h := G.graph_fst_eq_zero_snd hx' rfl
  exact (Jsc hε hc).injective (by rw [h, map_zero])

/-- The conjugate `J_ε⁻¹ G J_ε` of an operator `G` on `L²(dx dτ)`, as an operator on `H`. -/
def conjOp (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) : HSpace c ℝ →ₗ.[ℝ] HSpace c ℝ :=
  (conjGraph hε hc G).toLinearPMap

theorem graph_conjOp (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) :
    (conjOp hε hc G).graph = conjGraph hε hc G :=
  Submodule.toLinearPMap_graph_eq _ (conjGraph_functional hε hc G)

/-- `b ∈ dom(J⁻¹ G J)` iff `J b ∈ dom G` and `G (J b)` lies in the range of `J`. -/
theorem mem_domain_conjOp_iff (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) (b : HSpace c ℝ) :
    b ∈ (conjOp hε hc G).domain ↔
      ∃ h : Jsc hε hc b ∈ G.domain, G ⟨Jsc hε hc b, h⟩ ∈ LinearMap.range (Jsc hε hc).toLinearMap := by
  rw [LinearPMap.mem_domain_iff, graph_conjOp]
  constructor
  · rintro ⟨b', hb'⟩
    rw [mem_conjGraph, LinearPMap.mem_graph_iff] at hb'
    obtain ⟨y, hy1, hy2⟩ := hb'
    simp only at hy1 hy2
    have hmem : Jsc hε hc b ∈ G.domain := by rw [← hy1]; exact y.2
    refine ⟨hmem, b', ?_⟩
    have : (⟨Jsc hε hc b, hmem⟩ : G.domain) = y := Subtype.ext hy1.symm
    rw [this, hy2]
    rfl
  · rintro ⟨hmem, b', hb'⟩
    refine ⟨b', ?_⟩
    rw [mem_conjGraph, LinearPMap.mem_graph_iff]
    exact ⟨⟨Jsc hε hc b, hmem⟩, rfl, hb'.symm⟩

/-- `J_ε (J⁻¹ G J) b = G (J_ε b)` on the domain. -/
theorem Jsc_conjOp (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) (b : (conjOp hε hc G).domain)
    (h : Jsc hε hc b ∈ G.domain) :
    Jsc hε hc (conjOp hε hc G b) = G ⟨Jsc hε hc b, h⟩ := by
  have hg : ((b : HSpace c ℝ), conjOp hε hc G b) ∈ (conjOp hε hc G).graph :=
    LinearPMap.mem_graph _ b
  rw [graph_conjOp, mem_conjGraph, LinearPMap.mem_graph_iff] at hg
  obtain ⟨y, hy1, hy2⟩ := hg
  simp only at hy1 hy2
  have : (⟨Jsc hε hc b, h⟩ : G.domain) = y := Subtype.ext hy1.symm
  rw [this, hy2]

/-- A pair `(b, b')` with `J_ε b ∈ dom G` and `G (J_ε b) = J_ε b'` lies in the graph:
`b ∈ dom(J⁻¹ G J)` and `(J⁻¹ G J) b = b'`. -/
theorem conjOp_of_eq (G : PhysL2sc ε c →ₗ.[ℝ] PhysL2sc ε c) {b b' : HSpace c ℝ}
    (h : Jsc hε hc b ∈ G.domain) (hG : G ⟨Jsc hε hc b, h⟩ = Jsc hε hc b') :
    ∃ hb : b ∈ (conjOp hε hc G).domain, conjOp hε hc G ⟨b, hb⟩ = b' := by
  have hgr : (b, b') ∈ (conjOp hε hc G).graph := by
    rw [graph_conjOp, mem_conjGraph, LinearPMap.mem_graph_iff]
    exact ⟨⟨Jsc hε hc b, h⟩, rfl, hG⟩
  rw [LinearPMap.mem_graph_iff] at hgr
  obtain ⟨y, hy1, hy2⟩ := hgr
  simp only at hy1 hy2
  have hb : b ∈ (conjOp hε hc G).domain := by rw [← hy1]; exact y.2
  refine ⟨hb, ?_⟩
  have : (⟨b, hb⟩ : (conjOp hε hc G).domain) = y := Subtype.ext hy1.symm
  rw [this, hy2]

end Conj

end UnforcedLeray.B0221
