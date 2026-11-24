import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2_3
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound

/-!


Source of record: `the November 2 reference manuscript`,
lines 1809-1835. Mirrors `Gen1Bound` one derivative order higher.

`genDiff2Term5 ν v p = (ν s) (η ∂_η v)` and `genDiff2Term6 ν v p = (ν s) (v - E v)`, with
`v = flatAdjointRep ν μ h`. On `s > 0` the term `η ∂_η v` is rewritten through the causal
representation (`pdEta_causalAdjointRep`, `etaMul_causalAdjointRep`) as a causal integral plus a
second causal integral with weight `ν s`; `v - E v` is handled through `opE` (`|opE z| ≤ |z|`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226
open FlatAdjointElemAux

namespace PairCProof

/-- Equal `L²` norms for a.e. equal representatives. -/
theorem norm_toLp_eq_of_ae {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (h : f =ᵐ[μ] g) :
    ‖hf.toLp f‖ = ‖hg.toLp g‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_congr_ae h]

/-- Pointwise domination with a constant gives the `L²` norm domination. -/
theorem norm_toLp_le_mul_of_pointwise {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ x, ‖f x‖ ≤ K * ‖g x‖) :
    ‖hf.toLp f‖ ≤ K * ‖hg.toLp g‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  have hmono : eLpNorm f 2 μ ≤ eLpNorm (K • g) 2 μ := by
    apply eLpNorm_mono
    intro x
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
    exact h x
  rw [eLpNorm_const_smul] at hmono
  have hfin : eLpNorm g 2 μ ≠ ⊤ := hg.2.ne
  calc (eLpNorm f 2 μ).toReal ≤ (‖K‖ₑ * eLpNorm g 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hmono
    _ = K * (eLpNorm g 2 μ).toReal := by
        rw [ENNReal.toReal_mul, Real.enorm_eq_ofReal hK, ENNReal.toReal_ofReal hK]

/-- The coordinate projection `E` does not increase the norm. -/
theorem norm_opE_apply_le (f : Profile → MeridC) (p : Profile) : ‖opE f p‖ ≤ ‖f p‖ := by
  unfold opE
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_two]

/-- Measurability and `L²` membership of `E f` from `f`. -/
theorem memLp_opE {c : ℝ} {F : Profile → MeridC} (hF : MemLp F 2 (measureH c)) :
    MemLp (opE F) 2 (measureH c) := by
  have hT : Continuous (fun z : MeridC => (WithLp.toLp 2 ![z 0, 0] : MeridC)) := by
    fun_prop
  exact MemLp.of_le hF (hT.comp_aestronglyMeasurable hF.1)
    (Filter.Eventually.of_forall fun x => by
      unfold opE
      exact (norm_opE_apply_le F x : _))

/-! ### Causal pieces -/

/-- The unscaled causal adjoint `v₀ = causalAdjointRep ν μ θ₀ h`. -/
def pcV (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  causalAdjointRep ν μ (thetaWeight 0) h

/-- `causal θ₀ (η ∂_η h)`, the age-slice of the transverse derivative of `v`. -/
def pcA (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta h))

/-- `causal θ₁ (ν s ∂_η² h)`, the second transverse correction. -/
def pcB (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  causalAdjointRep ν μ (thetaWeight (0 + 1)) (nuSMul ν 1 (pdEta (pdEta h)))

/-- The combined representative of `η ∂_η v` on `s > 0`. -/
def pcF5 (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  pcA ν μ h - (2 : ℝ) • pcB ν μ h

/-- The representative of `v - E v` with `v = pcV`. -/
def pcF6 (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  pcV ν μ h - opE (pcV ν μ h)

theorem eq_pcV (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) :
    pcV ν μ h = causalAdjointRep ν μ (thetaWeight 0) (nuSMul ν 0 (etaMul^[0] h)) := by
  simp [pcV]

theorem eq_pcA (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) :
    pcA ν μ h = causalAdjointRep ν μ (thetaWeight 0) (nuSMul ν 0 (etaMul^[1] (pdEta h))) := by
  simp [pcA]

theorem mem_pcV {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4) {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    ∃ hV : MemLp (pcV ν μ h) 2 (measureH c),
      ‖hV.toLp (pcV ν μ h)‖ ≤ γs⁻¹ * flatProjMomentNorm c h := by
  have hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 0 h :=
    isBaseDeriv_base hh 0 (by decide)
  rw [eq_pcV]
  exact ⟨memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hu (j := 0) (by decide) 0 0,
    (norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh hu (j := 0) (by decide) 0 0).trans
      (by simp)⟩

theorem mem_pcA {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4) {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    ∃ hA : MemLp (pcA ν μ h) 2 (measureH c),
      ‖hA.toLp (pcA ν μ h)‖ ≤ γs⁻¹ * flatProjMomentNorm c h := by
  have hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 1 (pdEta h) :=
    isBaseDeriv_pdEta hh 0 (by decide)
  rw [eq_pcA]
  exact ⟨memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hu (j := 1) (by decide) 0 0,
    (norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh hu (j := 1) (by decide) 0 0).trans
      (by simp)⟩

theorem mem_pcB {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4) {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    ∃ hB : MemLp (pcB ν μ h) 2 (measureH c),
      ‖hB.toLp (pcB ν μ h)‖ ≤ γs⁻¹ * (ν * H1) * flatProjMomentNorm c h := by
  have hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 2 (pdEta (pdEta h)) :=
    isBaseDeriv_pdEta_pdEta hh 0 (by decide)
  exact ⟨memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hu (j := 0) (by decide) (0 + 1) 1,
    (norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh hu (j := 0) (by decide) (0 + 1) 1).trans
      (by simp)⟩

end PairCProof

open PairCProof

/-- **Pair C (`PartII-a:N04/2/2/3`)**: `L²` membership and polynomial `GammaBox` bound for
`genDiff2Term5` and `genDiff2Term6` applied to `flatAdjointRep ν μ h`. -/
theorem flatAdjointGen2PairC : UnforcedLeray.Short.PartIIa.N04_2_2_3.PairC := by
  refine ⟨5, 11, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have hμ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγs hμγ
  have hF0 : 0 ≤ flatProjMomentNorm c h := flatProjMomentNorm_nonneg c h
  have hγinv : 0 < γs⁻¹ := inv_pos.2 hγs
  -- `GammaBox` facts
  have hG1 : 1 ≤ GammaBox ν c σ H1 L1 M γs := one_le_GammaBox hν hc hσ hσH1 hL1 hM0 hγs
  have hγG : γs⁻¹ ≤ GammaBox ν c σ H1 L1 M γs :=
    inv_gammas_le_GammaBox ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM0
  have hνG : ν ≤ GammaBox ν c σ H1 L1 M γs := by
    unfold GammaBox
    have := inv_nonneg.2 hν.le
    have := inv_nonneg.2 hc.le
    have := inv_nonneg.2 hσ.le
    have := inv_nonneg.2 hγs.le
    linarith
  have hHG : H1 ≤ GammaBox ν c σ H1 L1 M γs := by
    unfold GammaBox
    have := inv_nonneg.2 hν.le
    have := inv_nonneg.2 hc.le
    have := inv_nonneg.2 hσ.le
    have := inv_nonneg.2 hγs.le
    linarith
  set G := GammaBox ν c σ H1 L1 M γs with hG
  have hG0 : 0 ≤ G := le_trans zero_le_one hG1
  have hYG : ν * H1 ≤ G ^ 2 := by
    have : ν * H1 ≤ G * G := mul_le_mul hνG hHG hH1.le hG0
    rw [sq]
    exact this
  have hY0 : 0 ≤ ν * H1 := (mul_pos hν hH1).le
  have hX0 : 0 ≤ γs⁻¹ * flatProjMomentNorm c h := mul_nonneg hγinv.le hF0
  -- causal pieces
  obtain ⟨hV, bV⟩ := mem_pcV hc hν hσ hσH1 hγs hμγ hh
  obtain ⟨hA, bA⟩ := mem_pcA hc hν hσ hσH1 hγs hμγ hh
  obtain ⟨hB, bB⟩ := mem_pcB hc hν hσ hσH1 hγs hμγ hh
  have hB0 : ∃ M0 : ℝ, ∀ q : Profile, ‖pdEta h q‖ ≤ M0 :=
    bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta hh 0 (by decide))
  have hB1 : ∃ M1 : ℝ, ∀ q : Profile, ‖pdEta (pdEta h) q‖ ≤ M1 :=
    bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdEta hh 0 (by decide))
  have hB2 : ∃ M2 : ℝ, ∀ q : Profile, ‖etaMul (pdEta h) q‖ ≤ M2 :=
    bdd_etaMul_of_isBaseDeriv hh (isBaseDeriv_pdEta hh 0 (by decide))
  -- pointwise identity for the transverse derivative of `v` on `s > 0`
  have hpt5 : ∀ p : Profile, 0 < p.1 →
      (p.2.2 : ℝ) • pdEta (flatAdjointRep ν μ h) p = pcF5 ν μ h p := by
    intro p hp
    rw [← causalAdjointRep_thetaWeight_zero ν μ h]
    rw [pdEta_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_base hh) hp]
    exact etaMul_causalAdjointRep hν hσ hσH1 hμ 0 (contDiff_pdEta hh.smooth)
      (support_s_pdEta hh.support_s) hB0 hB1 hB2 hp
  have hwA : ∀ q : Profile, H1 < q.1 → etaMul (pdEta h) q = 0 := fun q hq => by
    simp [etaMul, support_s_pdEta hh.support_s q (Or.inr hq)]
  have hwB : ∀ q : Profile, H1 < q.1 → nuSMul ν 1 (pdEta (pdEta h)) q = 0 := fun q hq => by
    simp [nuSMul, support_s_pdEta (support_s_pdEta hh.support_s) q (Or.inr hq)]
  have hsupp5 : ∀ p : Profile, H1 < p.1 → pcF5 ν μ h p = 0 := by
    intro p hp
    have hA0 : pcA ν μ h p = 0 :=
      causalAdjointRep_eq_zero_of_support_H1 hH1 ν μ (thetaWeight 0) hwA hp
    have hB0' : pcB ν μ h p = 0 :=
      causalAdjointRep_eq_zero_of_support_H1 hH1 ν μ (thetaWeight (0 + 1)) hwB hp
    simp [pcF5, hA0, hB0']
  have hF5 : MemLp (pcF5 ν μ h) 2 (measureH c) := hA.sub (hB.const_smul (2 : ℝ))
  have bF5 : ‖hF5.toLp (pcF5 ν μ h)‖ ≤ γs⁻¹ * flatProjMomentNorm c h +
      2 * (γs⁻¹ * (ν * H1) * flatProjMomentNorm c h) := by
    have h1 : ‖hF5.toLp (pcF5 ν μ h)‖ ≤ ‖hA.toLp (pcA ν μ h)‖ +
        ‖(hB.const_smul (2 : ℝ)).toLp ((2 : ℝ) • pcB ν μ h)‖ :=
      norm_toLp_sub_le hA (hB.const_smul (2 : ℝ))
    have h2 := norm_toLp_const_smul_eq (2 : ℝ) hB
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
    linarith [bA, bB]
  -- the term `v - E v`
  have hF6 : MemLp (pcF6 ν μ h) 2 (measureH c) := hV.sub (memLp_opE hV)
  have bF6 : ‖hF6.toLp (pcF6 ν μ h)‖ ≤ 2 * (γs⁻¹ * flatProjMomentNorm c h) := by
    have hpt : ∀ x, ‖pcF6 ν μ h x‖ ≤ 2 * ‖pcV ν μ h x‖ := by
      intro x
      have h1 := norm_sub_le (pcV ν μ h x) (opE (pcV ν μ h) x)
      have h2 := norm_opE_apply_le (pcV ν μ h) x
      show ‖pcV ν μ h x - opE (pcV ν μ h) x‖ ≤ 2 * ‖pcV ν μ h x‖
      linarith
    have h4 := norm_toLp_le_mul_of_pointwise hF6 hV (K := 2) (by norm_num) hpt
    linarith [bV]
  -- equality with the generator terms on `s > 0`
  have heq5 : ∀ p : Profile, 0 < p.1 →
      genDiff2Term5 ν (flatAdjointRep ν μ h) p = (ν * p.1) • pcF5 ν μ h p := by
    intro p hp
    show (ν * p.1) • ((p.2.2 : ℝ) • pdEta (flatAdjointRep ν μ h) p) = (ν * p.1) • pcF5 ν μ h p
    rw [hpt5 p hp]
  have hglob : flatAdjointRep ν μ h = pcV ν μ h :=
    (causalAdjointRep_thetaWeight_zero ν μ h).symm
  have heq6 : ∀ p : Profile, 0 < p.1 →
      genDiff2Term6 ν (flatAdjointRep ν μ h) p = (ν * p.1) • pcF6 ν μ h p := by
    intro p _
    rw [hglob]
    rfl
  have hsupp6 : ∀ p : Profile, H1 < p.1 → pcF6 ν μ h p = 0 := by
    intro p hp
    have hz : pcV ν μ h p = 0 :=
      causalAdjointRep_eq_zero_of_support_H1 hH1 ν μ (thetaWeight 0)
        (fun q hq => hh.support_s q (Or.inr hq)) hp
    show pcV ν μ h p - opE (pcV ν μ h) p = 0
    simp [opE, hz]
  have hG5 : MemLp (genDiff2Term5 ν (flatAdjointRep ν μ h)) 2 (measureH c) :=
    memLp_of_eqOn_pos_nuSMul_one hν hH1 hF5 hsupp5 heq5
  have hG6 : MemLp (genDiff2Term6 ν (flatAdjointRep ν μ h)) 2 (measureH c) :=
    memLp_of_eqOn_pos_nuSMul_one hν hH1 hF6 hsupp6 heq6
  have n5 : ‖hG5.toLp (genDiff2Term5 ν (flatAdjointRep ν μ h))‖ ≤
      (ν * H1) * ‖hF5.toLp (pcF5 ν μ h)‖ :=
    norm_toLp_of_eqOn_pos_nuSMul_one_le hν hH1 hF5 hsupp5 heq5
  have n6 : ‖hG6.toLp (genDiff2Term6 ν (flatAdjointRep ν μ h))‖ ≤
      (ν * H1) * ‖hF6.toLp (pcF6 ν μ h)‖ :=
    norm_toLp_of_eqOn_pos_nuSMul_one_le hν hH1 hF6 hsupp6 heq6
  -- numerical domination
  have h1 : ν * H1 ≤ G ^ 2 := hYG
  have h2 : γs⁻¹ * flatProjMomentNorm c h ≤ G * flatProjMomentNorm c h :=
    mul_le_mul_of_nonneg_right hγG hF0
  have hYX : (ν * H1) * (γs⁻¹ * flatProjMomentNorm c h) ≤ G ^ 3 * flatProjMomentNorm c h := by
    calc (ν * H1) * (γs⁻¹ * flatProjMomentNorm c h)
        ≤ G ^ 2 * (G * flatProjMomentNorm c h) := mul_le_mul h1 h2 hX0 (by positivity)
      _ = G ^ 3 * flatProjMomentNorm c h := by ring
  have hY2X : (ν * H1) * ((ν * H1) * (γs⁻¹ * flatProjMomentNorm c h)) ≤
      G ^ 5 * flatProjMomentNorm c h := by
    calc (ν * H1) * ((ν * H1) * (γs⁻¹ * flatProjMomentNorm c h))
        ≤ G ^ 2 * (G ^ 2 * (G * flatProjMomentNorm c h)) :=
          mul_le_mul h1 (mul_le_mul h1 h2 hX0 (by positivity)) (mul_nonneg hY0 hX0) (by positivity)
      _ = G ^ 5 * flatProjMomentNorm c h := by ring
  have hG35 : G ^ 3 * flatProjMomentNorm c h ≤ G ^ 5 * flatProjMomentNorm c h :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hG1 (by norm_num)) hF0
  have ha : ‖hG5.toLp (genDiff2Term5 ν (flatAdjointRep ν μ h))‖ ≤
      (ν * H1) * (γs⁻¹ * flatProjMomentNorm c h +
        2 * (γs⁻¹ * (ν * H1) * flatProjMomentNorm c h)) :=
    n5.trans (mul_le_mul_of_nonneg_left bF5 hY0)
  have hb : ‖hG6.toLp (genDiff2Term6 ν (flatAdjointRep ν μ h))‖ ≤
      (ν * H1) * (2 * (γs⁻¹ * flatProjMomentNorm c h)) :=
    n6.trans (mul_le_mul_of_nonneg_left bF6 hY0)
  refine ⟨hG5, hG6, ?_⟩
  nlinarith [ha, hb, hYX, hY2X, hG35]

end UnforcedLeray.Short.PartIIa
