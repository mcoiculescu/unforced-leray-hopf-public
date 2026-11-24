import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/a`: strong and adjoint-strong limits (SP 2962-2972)

Source: `the November 2 reference manuscript` (SP) 2919-2930, 2958-2972.

## The target `RelStrongLimit` is false as stated

`planarRelTransportW P m t s = e^{-λ(t-s)} T(t-s)` uses the *complex* eigenvalue
`λ = γ + iω` (`PlanarData.eigenvalue`; SP 595: `γ > 0`, `-2 < ω < 0`). The relative free
evolution of the source is damped by the *real* rate `β₀ = γ + Re κ/θ` (SP 2919), and its planar
limit is `e^{-γ(t-s)} T(t-s)` (SP 2927: `𝒬(𝓛-γ)𝒬-𝒫`). In Lean, `IsPeriodizedRelFreeBlockEvol`
gives, for real `W` supported in the cell and agreeing there with `J⁻¹ f` (`f` a cylinder test,
whose free flow `ω₀` exists by `IIb.free_cyl_exists_unique`), the value
`(clockN P ν s t)⁻¹ · periodizedExt d_s d_t (J⁻¹ ω₀(t)) W`, which is real valued (`clockN` real,
`ω₀` real). For a real radial `W ≠ 0` (so `T(t)W = W`, `transportExp_zero_sector`) and
`u := F_rel τ σ (Π W)` real, `‖u - e^{-λ(τ-σ)} W‖ ≥ e^{-γ(τ-σ)} |sin(ω(τ-σ))| ‖W‖`, which is
bounded below independently of `ν`, `b` (take `σ = 0`, `τ = B = 1`: `sin ω ≠ 0`). So the first
conjunct fails for small `ε` in every instance of the hypotheses (seed kernels, a planar reference,
small `ν` with `PerFrameFacts`, a BUC train, a block, and a periodized free evolution). The
second conjunct fails likewise.

## What is proved here

* `planarRelTransportRe`: the corrected limit `e^{-γ(t-s)} T(t-s)`, `γ = Re λ`.
* `RelStrongLimitTo κ T₀`: the statement of `RelStrongLimit` for an arbitrary limit family `T₀`;
  `RelStrongLimit κ ↔ RelStrongLimitTo κ planarRelTransportW` (`Iff.rfl`).
* Two leaves (SP 2958-2964):
  - `RelFreeTestLimitTo κ T₀` (SP 2962-2964, "compact smooth tests and Duhamel give direct strong
    convergence ... uniformly in the entrance time"): convergence `F_rel τ σ Φ → T₀ τ σ Φ` for
    compactly supported smooth `Φ`;
  - `RelFreeNormLimit κ` (SP 2958-2961, 2964-2965, "the undamped norms have limiting upper bound
    one"): `‖F_rel τ σ‖ ≤ e^{-γ(τ-σ)} + ε` in the successive limit
    (from `FrameBlockContractSub.relFreeMovingEnergy` and `norm_extDilW_cellLen_le_exp`).
* `relStrongLimitTo_of`: for every limit family with `‖T₀‖ ≤ e^{-γ(t-s)}`,
  `T₀ T₀† = e^{-2γ(t-s)}` and totally bounded adjoint orbits (`IsRelLimitFamily`), the two leaves
  imply `RelStrongLimitTo κ T₀` (density via `Lp.dense_hasCompactSupport_contDiff`, entrance cell
  projection, finite nets, and the adjoint identity `norm_adjoint_sub_sq_eq`, SP 2966-2972).
* `relStrongLimitRe_of` (corrected target) and `relStrongLimit_of` (original target; its leaf
  `RelFreeTestLimitTo κ planarRelTransportW` is false for the reason above).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

namespace StrongA

/-! ## 1. The transport group is unitary -/

theorem transportGroupW_comp_neg (M t : ℝ) :
    Planar.transportGroupW M t ∘L Planar.transportGroupW M (-t) = 1 := by
  rw [← Planar.transportGroupW_add, add_neg_cancel, Planar.transportGroupW_zero]

theorem transportGroupW_neg_comp (M t : ℝ) :
    Planar.transportGroupW M (-t) ∘L Planar.transportGroupW M t = 1 := by
  rw [← Planar.transportGroupW_add, neg_add_cancel, Planar.transportGroupW_zero]

theorem norm_transportGroupW_apply (M t : ℝ) (x : Planar.L2w M) :
    ‖Planar.transportGroupW M t x‖ = ‖x‖ := by
  have hle : ∀ (s : ℝ) (y : Planar.L2w M), ‖Planar.transportGroupW M s y‖ ≤ ‖y‖ := by
    intro s y
    calc ‖Planar.transportGroupW M s y‖ ≤ ‖Planar.transportGroupW M s‖ * ‖y‖ :=
          (Planar.transportGroupW M s).le_opNorm y
      _ ≤ 1 * ‖y‖ :=
          mul_le_mul_of_nonneg_right (Planar.norm_transportGroupW_le M s) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  refine le_antisymm (hle t x) ?_
  calc ‖x‖ = ‖Planar.transportGroupW M (-t) (Planar.transportGroupW M t x)‖ := by
        rw [← ContinuousLinearMap.comp_apply, transportGroupW_neg_comp,
          one_apply_eq_self]
    _ ≤ ‖Planar.transportGroupW M t x‖ := hle _ _

theorem inner_transportGroupW (M t : ℝ) (x y : Planar.L2w M) :
    ⟪Planar.transportGroupW M t x, Planar.transportGroupW M t y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : Planar.L2w M →ₗᵢ[ℂ] Planar.L2w M :=
    { toLinearMap := (Planar.transportGroupW M t : Planar.L2w M →ₗ[ℂ] Planar.L2w M)
      norm_map' := norm_transportGroupW_apply M t }
  exact L.inner_map_map x y

/-- `T(t)† = T(-t)`: radial transport is unitary (SP 2964-2965). -/
theorem adjoint_transportGroupW (M t : ℝ) :
    ContinuousLinearMap.adjoint (Planar.transportGroupW M t) = Planar.transportGroupW M (-t) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  calc ⟪Planar.transportGroupW M (-t) x, y⟫_ℂ
      = ⟪Planar.transportGroupW M t (Planar.transportGroupW M (-t) x),
          Planar.transportGroupW M t y⟫_ℂ := (inner_transportGroupW M t _ _).symm
    _ = ⟪x, Planar.transportGroupW M t y⟫_ℂ := by
        rw [← ContinuousLinearMap.comp_apply, transportGroupW_comp_neg,
          one_apply_eq_self]

theorem adjoint_smul_transportGroupW (M t : ℝ) (z : ℂ) :
    ContinuousLinearMap.adjoint (z • Planar.transportGroupW M t) =
      (starRingEnd ℂ z) • Planar.transportGroupW M (-t) := by
  rw [map_smulₛₗ, adjoint_transportGroupW]

theorem smul_transportGroupW_comp_adjoint (M t : ℝ) (z : ℂ) :
    (z • Planar.transportGroupW M t) ∘L ContinuousLinearMap.adjoint (z • Planar.transportGroupW M t) =
      ((‖z‖ ^ 2 : ℝ) : ℂ) • (1 : Planar.L2w M →L[ℂ] Planar.L2w M) := by
  rw [adjoint_smul_transportGroupW, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, transportGroupW_comp_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ## 2. Limit families -/

/-- A family of limiting relative free evolutions `T₀ P m t s` on `Planar.L2w m`. -/
abbrev LimitFamily : Type :=
  PlanarData → ∀ m : ℝ, ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m

/-- The abstract properties of a limit family used by the adjoint-strong argument (SP 2964-2972):
norm at most `e^{-γ(t-s)}`, `T₀ T₀† = e^{-2γ(t-s)}` (a multiple of a unitary), and totally bounded
adjoint orbits on blocks. -/
structure IsRelLimitFamily (T₀ : LimitFamily) : Prop where
  norm_le : ∀ (P : PlanarData) (m t s : ℝ), ‖T₀ P m t s‖ ≤ Real.exp (-P.eigenvalue.re * (t - s))
  comp_adjoint : ∀ (P : PlanarData) (m t s : ℝ),
    T₀ P m t s ∘L ContinuousLinearMap.adjoint (T₀ P m t s) =
      ((Real.exp (-P.eigenvalue.re * (t - s)) ^ 2 : ℝ) : ℂ) •
        (1 : Planar.L2w m →L[ℂ] Planar.L2w m)
  adjoint_tb : ∀ (P : PlanarData) (m : ℝ) (W : Planar.L2w m) (B : ℝ),
    TotallyBounded {v : Planar.L2w m | ∃ σ τ : ℝ, 0 ≤ σ ∧ σ ≤ τ ∧ τ ≤ B ∧
      v = ContinuousLinearMap.adjoint (T₀ P m τ σ) W}

/-- `z(t - s) • T(t - s)` for a scalar profile `z`. -/
def smulTransport (z : PlanarData → ℝ → ℂ) : LimitFamily :=
  fun P m t s => z P (t - s) • Planar.transportGroupW m (t - s)

theorem isRelLimitFamily_smulTransport (z : PlanarData → ℝ → ℂ) (hz : ∀ P, Continuous (z P))
    (hnorm : ∀ P u, ‖z P u‖ = Real.exp (-P.eigenvalue.re * u)) :
    IsRelLimitFamily (smulTransport z) where
  norm_le P m t s := by
    unfold smulTransport
    rw [norm_smul, hnorm]
    calc Real.exp (-P.eigenvalue.re * (t - s)) * ‖Planar.transportGroupW m (t - s)‖
        ≤ Real.exp (-P.eigenvalue.re * (t - s)) * 1 :=
          mul_le_mul_of_nonneg_left (Planar.norm_transportGroupW_le m (t - s))
            (Real.exp_pos _).le
      _ = Real.exp (-P.eigenvalue.re * (t - s)) := mul_one _
  comp_adjoint P m t s := by
    unfold smulTransport
    rw [smul_transportGroupW_comp_adjoint, hnorm]
  adjoint_tb P m W B := by
    let g : ℝ → Planar.L2w m := fun u =>
      (starRingEnd ℂ (z P u)) • Planar.transportGroupW m (-u) W
    have hg : Continuous g :=
      (Complex.continuous_conj.comp (hz P)).smul
        ((Planar.continuous_transportGroupW_apply m W).comp continuous_neg)
    refine (((isCompact_Icc (a := (0 : ℝ)) (b := B)).image hg).totallyBounded).subset ?_
    rintro v ⟨σ, τ, hσ, hστ, hτ, rfl⟩
    refine ⟨τ - σ, ⟨sub_nonneg.2 hστ, by linarith⟩, ?_⟩
    simp only [g, smulTransport, adjoint_smul_transportGroupW, ContinuousLinearMap.smul_apply]

theorem planarRelTransportW_eq_smulTransport :
    (planarRelTransportW : LimitFamily) =
      smulTransport fun P u => Complex.exp (-P.eigenvalue * (u : ℂ)) := rfl

theorem isRelLimitFamily_planarRelTransportW : IsRelLimitFamily planarRelTransportW := by
  rw [planarRelTransportW_eq_smulTransport]
  refine isRelLimitFamily_smulTransport _ (fun P => ?_) (fun P u => ?_)
  · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  · rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]

/-- **Corrected limit** (SP 2919, 2927): `e^{-γ(t-s)} T(t-s)` with the real rate `γ = Re λ`. -/
theorem planarRelTransportRe_eq_smulTransport :
    (planarRelTransportRe : LimitFamily) =
      smulTransport fun P u => ((Real.exp (-P.eigenvalue.re * u) : ℝ) : ℂ) := rfl

/-- Qualified alias kept for the leaf targets that name `StrongA.planarRelTransportRe`
(the definition lives in `OrgSplit3`, beside `RelStrongLimit`). -/
protected abbrev planarRelTransportRe : LimitFamily := OrgSplit3.planarRelTransportRe

theorem isRelLimitFamily_planarRelTransportRe : IsRelLimitFamily planarRelTransportRe := by
  rw [planarRelTransportRe_eq_smulTransport]
  refine isRelLimitFamily_smulTransport _ (fun P => ?_) (fun P u => ?_)
  · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-! ## 3. Entrance cell projection -/

theorem norm_cellProjW_le (m d : ℝ) : ‖cellProjW m d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem cellProjW_eq_self {m d : ℝ} (W : Planar.L2w m) {Φ : ℂ → ℂ} (hW : ⇑W =ᵐ[volume] Φ)
    (hΦ : ∀ z, Φ z ≠ 0 → cToPlane z ∈ B0579.cell d) : cellProjW m d W = W := by
  have hW' : ⇑W =ᵐ[Planar.wMeasure m] Φ := (Planar.wMeasure_ac m).ae_eq hW
  have happ : cellProjW m d W = ((Lp.memLp W).indicator (measurableSet_cellC d)).toLp _ := rfl
  rw [happ]
  refine Lp.ext ?_
  filter_upwards [((Lp.memLp W).indicator (measurableSet_cellC d)).coeFn_toLp, hW'] with z h1 h2
  rw [h1]
  by_cases hz : z ∈ {z : ℂ | cToPlane z ∈ B0579.cell d}
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz, h2]
    by_contra hne
    exact hz (hΦ z fun h => hne h.symm)

/-- In the successive limit the entrance cell is long: `ν⁻¹ ≤ d(t₁)` for `ν ≤ 1 ≤ b ≤ θ(t₂)`. -/
theorem inv_le_cellLen {ν t₁ t₂ b : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (ht₁ : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (hb : 1 ≤ b) (hbt : b ≤ clockTheta ν t₂) :
    ν⁻¹ ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁) := by
  unfold cellLen
  have ha1 : 0 < clockA ν t₁ := by unfold clockA; positivity
  have ha2 : 0 < clockA ν t₂ := by unfold clockA; have := mul_nonneg hν.le (ht₁.trans h12); linarith
  have h1 : ν * clockA ν t₂ ≤ 1 := by
    have h := hb.trans hbt
    unfold clockTheta at h
    rwa [one_le_inv₀ (mul_pos hν ha2)] at h
  have h2 : clockA ν t₁ ≤ clockA ν t₂ := by
    unfold clockA; nlinarith
  have hνinv : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have h3 : clockA ν t₁ ≤ ν⁻¹ := by
    have : ν * clockA ν t₁ ≤ 1 := (mul_le_mul_of_nonneg_left h2 hν.le).trans h1
    rw [← one_div, le_div_iff₀ hν]
    linarith
  have h4 : Real.sqrt (clockA ν t₁) ≤ ν⁻¹ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hrpow : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by
    rw [Real.rpow_neg hν.le]
    norm_cast
  rw [hrpow, le_div_iff₀ (Real.sqrt_pos.2 ha1)]
  calc ν⁻¹ * Real.sqrt (clockA ν t₁) ≤ ν⁻¹ * ν⁻¹ :=
        mul_le_mul_of_nonneg_left h4 (inv_nonneg.2 hν.le)
    _ = (ν ^ 2)⁻¹ := by rw [sq, mul_inv]

/-- Compactly supported functions lie in long entrance cells. -/
theorem mem_cell_of_norm_le {d R : ℝ} (hd : 2 * R < d) {z : ℂ} (hz : ‖z‖ ≤ R) :
    cToPlane z ∈ B0579.cell d := by
  have hre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hz
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
  · simp only [cToPlane]; linarith [neg_abs_le z.re]
  · simp only [cToPlane]; linarith [le_abs_self z.re]

/-! ## 4. Successive-limit combinators -/

/-- The block property type of `SuccBlock`. -/
abbrev BlockProp : Type :=
  ∀ ν : ℝ, UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)) → ℝ → ℝ → Prop

theorem succBlock_mono {κ : PlanarFrameKernels} {m K B : ℝ} {Q₁ Q₂ : BlockProp}
    (h : SuccBlock κ m K B Q₁) (H : ∀ ν tr t₁ t₂, Q₁ ν tr t₁ t₂ → Q₂ ν tr t₁ t₂) :
    SuccBlock κ m K B Q₂ := by
  obtain ⟨b₀, hb₀, H₀⟩ := h
  refine ⟨b₀, hb₀, fun b hb => ?_⟩
  obtain ⟨ν₀, hν₀, G⟩ := H₀ b hb
  exact ⟨ν₀, hν₀, fun ν hν hF tr htr t₁ t₂ h0 h12 hbt hB =>
    H _ _ _ _ (G ν hν hF tr htr t₁ t₂ h0 h12 hbt hB)⟩

/-- Weakening with the side conditions `ν ≤ ν₁`, `1 ≤ b ≤ θ(t₂)`, `0 ≤ t₁ ≤ t₂`. -/
theorem succBlock_mono' {κ : PlanarFrameKernels} {m K B : ℝ} {Q₁ Q₂ : BlockProp}
    (h : SuccBlock κ m K B Q₁) {ν₁ : ℝ} (hν₁ : 0 < ν₁)
    (H : ∀ ν : ℝ, 0 < ν → ν ≤ ν₁ → ∀ b : ℝ, 1 ≤ b →
      ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ), 0 ≤ t₁ → t₁ ≤ t₂ →
        b ≤ clockTheta ν t₂ → Q₁ ν tr t₁ t₂ → Q₂ ν tr t₁ t₂) :
    SuccBlock κ m K B Q₂ := by
  obtain ⟨b₀, hb₀, H₀⟩ := h
  refine ⟨b₀, hb₀, fun b hb => ?_⟩
  obtain ⟨ν₀, hν₀, G⟩ := H₀ b hb
  refine ⟨min ν₀ ν₁, lt_min hν₀ hν₁, fun ν hν hF tr htr t₁ t₂ h0 h12 hbt hB => ?_⟩
  exact H ν hν.1 (hν.2.trans (min_le_right _ _)) b (hb₀.trans hb) tr t₁ t₂ h0 h12 hbt
    (G ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ hF tr htr t₁ t₂ h0 h12 hbt hB)

theorem succBlock_and {κ : PlanarFrameKernels} {m K B : ℝ} {Q₁ Q₂ : BlockProp}
    (h₁ : SuccBlock κ m K B Q₁) (h₂ : SuccBlock κ m K B Q₂) :
    SuccBlock κ m K B fun ν tr t₁ t₂ => Q₁ ν tr t₁ t₂ ∧ Q₂ ν tr t₁ t₂ := by
  obtain ⟨b₁, hb₁, H₁⟩ := h₁
  obtain ⟨b₂, hb₂, H₂⟩ := h₂
  refine ⟨max b₁ b₂, hb₁.trans (le_max_left _ _), fun b hb => ?_⟩
  obtain ⟨ν₁, hν₁, G₁⟩ := H₁ b ((le_max_left _ _).trans hb)
  obtain ⟨ν₂, hν₂, G₂⟩ := H₂ b ((le_max_right _ _).trans hb)
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν hF tr htr t₁ t₂ h0 h12 hbt hB => ⟨?_, ?_⟩⟩
  · exact G₁ ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ hF tr htr t₁ t₂ h0 h12 hbt hB
  · exact G₂ ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩ hF tr htr t₁ t₂ h0 h12 hbt hB

theorem succBlock_finset {κ : PlanarFrameKernels} {m K B : ℝ} {ι : Type*} (s : Finset ι)
    (Q : ι → BlockProp) (h : ∀ i ∈ s, SuccBlock κ m K B (Q i)) :
    SuccBlock κ m K B fun ν tr t₁ t₂ => ∀ i ∈ s, Q i ν tr t₁ t₂ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, le_rfl, fun b _ => ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ _ _ i hi =>
      absurd hi (Finset.notMem_empty i)⟩⟩
  | insert a s ha ih =>
    refine succBlock_mono (succBlock_and (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) ?_
    rintro ν tr t₁ t₂ ⟨h1, h2⟩ i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h1
    · exact h2 i hi

/-! ## 5. The statements -/

/-- `RelStrongLimit` (SP 2962-2972) with an arbitrary limit family `T₀` in place of
`planarRelTransportW`. -/
def RelStrongLimitTo (κ : PlanarFrameKernels) (T₀ : LimitFamily) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B : ℝ, 0 < B →
  ∀ ε : ℝ, 0 < ε → ∀ W : Planar.L2w m,
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
          ‖F_rel τ σ (cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W) -
              T₀ P m τ σ W‖ < ε ∧
          ‖ContinuousLinearMap.adjoint
                (F_rel τ σ ∘L cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))) W -
              ContinuousLinearMap.adjoint (T₀ P m τ σ) W‖ < ε

theorem relStrongLimitTo_planarRelTransportRe (κ : PlanarFrameKernels) :
    RelStrongLimitTo κ planarRelTransportRe ↔ RelStrongLimit κ := Iff.rfl

/-- **Corrected target** (SP 2919, 2927, 2962-2972): the limit is `e^{-γ(t-s)} T(t-s)`. -/
def RelStrongLimitRe (κ : PlanarFrameKernels) : Prop := RelStrongLimitTo κ planarRelTransportRe

/-- **Leaf D** (SP 2962-2964): on each fixed block, compact smooth tests give direct strong
convergence of the periodized relative free evolution to the limit family `T₀`, in the successive
limit `ν → 0` after `b → ∞`, uniformly in train, entrance time and `0 ≤ σ ≤ τ ≤ B`. -/
def RelFreeTestLimitTo (κ : PlanarFrameKernels) (T₀ : LimitFamily) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B : ℝ, 0 < B →
  ∀ ε : ℝ, 0 < ε →
  ∀ Φ : ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
  ∀ W : Planar.L2w m, (⇑W =ᵐ[volume] Φ) →
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
          ‖F_rel τ σ W - T₀ P m τ σ W‖ < ε

/-- **Leaf N** (SP 2958-2961, 2964-2965: the undamped norms have limiting upper bound one):
`‖F_rel τ σ‖ ≤ e^{-γ(τ-σ)} + ε` in the successive limit (`eq:short-causal-free-moving` for the
periodized evolution, interior part `relFreeMovingEnergy`, exterior part
`norm_extDilW_cellLen_le_exp`). -/
def RelFreeNormLimit (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B : ℝ, 0 < B →
  ∀ ε : ℝ, 0 < ε →
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
          ‖F_rel τ σ‖ ≤ Real.exp (-P.eigenvalue.re * (τ - σ)) + ε

/-! ## 6. Proof of the assembly -/

/-- Smooth compactly supported elements are dense in `Planar.L2w m`
(`Lp.dense_hasCompactSupport_contDiff`; `wMeasure m` is locally finite). -/
theorem dense_smoothTests (m : ℝ) :
    Dense {f : Planar.L2w m | ∃ g : ℂ → ℂ, f =ᵐ[Planar.wMeasure m] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g} := by
  haveI : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  exact MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)

/-- Strong convergence on one compactly supported smooth test, through the entrance cell
projection (the cell contains the support for small `ν`). -/
theorem strong_test {κ : PlanarFrameKernels} {T₀ : LimitFamily} (hD : RelFreeTestLimitTo κ T₀)
    (hκ : IsSeedKernels κ) {P : PlanarData} (hP : IsPlanarReference P) {m : ℝ} (hm : 8 < m)
    (K : ℝ) {B : ℝ} (hB : 0 < B) {Φ : ℂ → ℂ} (hΦs : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (y : Planar.L2w m) (hy : ⇑y =ᵐ[volume] Φ) {η : ℝ} (hη : 0 < η) :
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
          ‖F_rel τ σ (cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) y) -
            T₀ P m τ σ y‖ < η := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z, Φ z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz => ?_⟩
    have h := hR (subset_tsupport Φ hz)
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hν₁ : 0 < min 1 (1 / (2 * |R| + 1)) := lt_min one_pos (by positivity)
  refine succBlock_mono' (hD hκ P hP m hm K B hB η hη Φ hΦs hΦc y hy) hν₁ ?_
  intro ν hν hνle b hb tr t₁ t₂ ht₁ h12 hbt hQ F_rel hF σ τ hσ hστ hτ
  have hd : 2 * R < cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁) := by
    have h1 := inv_le_cellLen hν (hνle.trans (min_le_left _ _)) ht₁ h12 hb hbt
    have h2 : ν ≤ 1 / (2 * |R| + 1) := hνle.trans (min_le_right _ _)
    have h3 : 2 * |R| + 1 ≤ ν⁻¹ := by
      rw [le_div_iff₀ (by positivity)] at h2
      rw [← one_div, le_div_iff₀ hν]
      linarith
    linarith [le_abs_self R]
  have hproj : cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) y = y :=
    cellProjW_eq_self y hy fun z hz => mem_cell_of_norm_le hd (hR z hz)
  rw [hproj]
  exact hQ F_rel hF σ τ hσ hστ hτ

/-- Strong convergence, uniformly on a totally bounded set of vectors (finite net of smooth
tests, SP 2964 "density extends the convergence"). -/
theorem strong_tb {κ : PlanarFrameKernels} {T₀ : LimitFamily} (hT : IsRelLimitFamily T₀)
    (hD : RelFreeTestLimitTo κ T₀) (hN : RelFreeNormLimit κ) (hκ : IsSeedKernels κ)
    {P : PlanarData} (hP : IsPlanarReference P) {m : ℝ} (hm : 8 < m) (K : ℝ) {B : ℝ}
    (hB : 0 < B) {S : Set (Planar.L2w m)} (hS : TotallyBounded S) {η : ℝ} (hη : 0 < η) :
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B → ∀ u ∈ S,
          ‖F_rel τ σ (cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) u) -
            T₀ P m τ σ u‖ < η := by
  set CB : ℝ := Real.exp (|P.eigenvalue.re| * B) with hCB
  have hCB0 : 0 < CB := Real.exp_pos _
  set η₁ : ℝ := η / (4 * (CB + 1)) with hη₁
  have hη₁0 : 0 < η₁ := by positivity
  obtain ⟨t₀, ht₀fin, ht₀⟩ := Metric.totallyBounded_iff.1 hS (η₁ / 2) (by positivity)
  have hdense := dense_smoothTests m
  choose g hgD hgdist using fun y : Planar.L2w m => hdense.exists_dist_lt y (half_pos hη₁0)
  have hpts := succBlock_finset (κ := κ) (m := m) (K := K) (B := B) ht₀fin.toFinset
    (fun y ν tr t₁ _t₂ => ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
          ‖F_rel τ σ (cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) (g y)) -
            T₀ P m τ σ (g y)‖ < η / 4) fun y _ => by
    obtain ⟨Φ, hΦae, hΦc, hΦs⟩ := hgD y
    exact strong_test hD hκ hP hm K hB hΦs hΦc (g y) ((Planar.volume_ac m).ae_eq hΦae)
      (by positivity)
  have hnorm := hN hκ P hP m hm K B hB 1 one_pos
  refine succBlock_mono (succBlock_and hpts hnorm) ?_
  rintro ν tr t₁ t₂ ⟨h1, h2⟩ F_rel hF σ τ hσ hστ hτ u hu
  obtain ⟨y, hyt, hyu⟩ := Set.mem_iUnion₂.1 (ht₀ hu)
  set Pc := cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
  have hc : Real.exp (-P.eigenvalue.re * (τ - σ)) ≤ CB := by
    apply Real.exp_le_exp.2
    have h0 : 0 ≤ τ - σ := sub_nonneg.2 hστ
    have h0' : τ - σ ≤ B := by linarith
    have := neg_abs_le P.eigenvalue.re
    nlinarith [abs_nonneg P.eigenvalue.re]
  have hF1 : ‖F_rel τ σ‖ ≤ CB + 1 := (h2 F_rel hF σ τ hσ hστ hτ).trans (by linarith)
  have hT1 : ‖T₀ P m τ σ‖ ≤ CB := (hT.norm_le P m τ σ).trans hc
  have hgy : dist u (g y) < η₁ := by
    have h3 : dist u y < η₁ / 2 := hyu
    have h4 := hgdist y
    linarith [dist_triangle u y (g y)]
  have hy' := h1 y (ht₀fin.mem_toFinset.2 hyt) F_rel hF σ τ hσ hστ hτ
  have hsplit : F_rel τ σ (Pc u) - T₀ P m τ σ u =
      F_rel τ σ (Pc (u - g y)) + (F_rel τ σ (Pc (g y)) - T₀ P m τ σ (g y)) +
        T₀ P m τ σ (g y - u) := by
    simp only [map_sub]; abel
  rw [hsplit]
  have hug : ‖u - g y‖ ≤ η₁ := by rw [← dist_eq_norm]; exact hgy.le
  have hgu : ‖g y - u‖ ≤ η₁ := by rw [← dist_eq_norm, dist_comm]; exact hgy.le
  have e1 : ‖F_rel τ σ (Pc (u - g y))‖ ≤ (CB + 1) * η₁ := by
    calc ‖F_rel τ σ (Pc (u - g y))‖ ≤ ‖F_rel τ σ‖ * ‖Pc (u - g y)‖ := (F_rel τ σ).le_opNorm _
      _ ≤ (CB + 1) * η₁ := by
          refine mul_le_mul hF1 ?_ (norm_nonneg _) (by positivity)
          calc ‖Pc (u - g y)‖ ≤ ‖Pc‖ * ‖u - g y‖ := Pc.le_opNorm _
            _ ≤ 1 * η₁ := mul_le_mul (norm_cellProjW_le _ _) hug (norm_nonneg _) zero_le_one
            _ = η₁ := one_mul _
  have e3 : ‖T₀ P m τ σ (g y - u)‖ ≤ CB * η₁ := by
    calc ‖T₀ P m τ σ (g y - u)‖ ≤ ‖T₀ P m τ σ‖ * ‖g y - u‖ := (T₀ P m τ σ).le_opNorm _
      _ ≤ CB * η₁ := mul_le_mul hT1 hgu (norm_nonneg _) hCB0.le
  have hη₁' : (CB + 1) * η₁ = η / 4 := by rw [hη₁]; field_simp
  have hη₁'' : CB * η₁ ≤ η / 4 := by nlinarith
  calc ‖F_rel τ σ (Pc (u - g y)) + (F_rel τ σ (Pc (g y)) - T₀ P m τ σ (g y)) +
        T₀ P m τ σ (g y - u)‖
      ≤ ‖F_rel τ σ (Pc (u - g y))‖ + ‖F_rel τ σ (Pc (g y)) - T₀ P m τ σ (g y)‖ +
          ‖T₀ P m τ σ (g y - u)‖ := norm_add₃_le
    _ < η := by linarith

/-- **Assembly**: for a limit family with `IsRelLimitFamily`, leaves D and N give the strong and
adjoint-strong limits (SP 2962-2972, adjoint step via `norm_adjoint_sub_sq_eq`). -/
theorem relStrongLimitTo_of (κ : PlanarFrameKernels) {T₀ : LimitFamily}
    (hT : IsRelLimitFamily T₀) (hD : RelFreeTestLimitTo κ T₀) (hN : RelFreeNormLimit κ) :
    RelStrongLimitTo κ T₀ := by
  intro hκ P hP m hm K B hB ε hε W
  set CB : ℝ := Real.exp (|P.eigenvalue.re| * B) with hCB
  have hCB0 : 0 < CB := Real.exp_pos _
  set Nw : ℝ := ‖W‖ + 1 with hNw
  have hNw0 : 0 < Nw := by positivity
  set η : ℝ := min 1 (ε ^ 2 / (4 * (2 * CB + 1) * Nw ^ 2)) with hηdef
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  set η' : ℝ := ε ^ 2 / (4 * Nw) with hη'def
  have hη'0 : 0 < η' := by positivity
  have hW := strong_tb hT hD hN hκ hP hm K hB (Set.finite_singleton W).totallyBounded hε
  have hA := strong_tb hT hD hN hκ hP hm K hB (hT.adjoint_tb P m W B) hη'0
  have hn := hN hκ P hP m hm K B hB η hη0
  refine succBlock_mono (succBlock_and hW (succBlock_and hA hn)) ?_
  rintro ν tr t₁ t₂ ⟨h1, h2, h3⟩ F_rel hF σ τ hσ hστ hτ
  refine ⟨h1 F_rel hF σ τ hσ hστ hτ W (Set.mem_singleton W), ?_⟩
  set Pc := cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
  set A := F_rel τ σ ∘L Pc with hAdef
  set T := T₀ P m τ σ with hTdef
  set c : ℝ := Real.exp (-P.eigenvalue.re * (τ - σ)) with hcdef
  have hc0 : 0 < c := Real.exp_pos _
  have hc : c ≤ CB := by
    apply Real.exp_le_exp.2
    have h0 : 0 ≤ τ - σ := sub_nonneg.2 hστ
    have h0' : τ - σ ≤ B := by linarith
    have := neg_abs_le P.eigenvalue.re
    nlinarith [abs_nonneg P.eigenvalue.re]
  set v := ContinuousLinearMap.adjoint T W with hvdef
  have hv : v ∈ {v : Planar.L2w m | ∃ σ τ : ℝ, 0 ≤ σ ∧ σ ≤ τ ∧ τ ≤ B ∧
      v = ContinuousLinearMap.adjoint (T₀ P m τ σ) W} := ⟨σ, τ, hσ, hστ, hτ, rfl⟩
  have hFv : ‖A v - T v‖ < η' := h2 F_rel hF σ τ hσ hστ hτ v hv
  have hTv : T v = ((c ^ 2 : ℝ) : ℂ) • W := by
    have h := congrArg (fun L : Planar.L2w m →L[ℂ] Planar.L2w m => L W) (hT.comp_adjoint P m τ σ)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      one_apply_eq_self] using h
  have hTn : ‖T‖ ≤ c := hT.norm_le P m τ σ
  -- `‖v‖ = c ‖W‖`
  have hv_le : ‖v‖ ≤ c * ‖W‖ := by
    calc ‖v‖ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖W‖ := (ContinuousLinearMap.adjoint T).le_opNorm W
      _ = ‖T‖ * ‖W‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ c * ‖W‖ := mul_le_mul_of_nonneg_right hTn (norm_nonneg W)
  have hv_ge : c * ‖W‖ ≤ ‖v‖ := by
    have h : ‖T v‖ ≤ c * ‖v‖ := (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hTn (norm_nonneg v))
    rw [hTv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    nlinarith
  have hv_sq : ‖v‖ ^ 2 = c ^ 2 * ‖W‖ ^ 2 := by
    rw [le_antisymm hv_le hv_ge]; ring
  -- `‖A‖ ≤ c + η`
  have hA_le : ‖A‖ ≤ c + η := by
    calc ‖A‖ ≤ ‖F_rel τ σ‖ * ‖Pc‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (c + η) * 1 := mul_le_mul (h3 F_rel hF σ τ hσ hστ hτ) (norm_cellProjW_le _ _)
          (norm_nonneg _) (by positivity)
      _ = c + η := mul_one _
  have hAW : ‖ContinuousLinearMap.adjoint A W‖ ≤ (c + η) * ‖W‖ := by
    calc ‖ContinuousLinearMap.adjoint A W‖ ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖W‖ :=
          (ContinuousLinearMap.adjoint A).le_opNorm W
      _ = ‖A‖ * ‖W‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ (c + η) * ‖W‖ := mul_le_mul_of_nonneg_right hA_le (norm_nonneg _)
  -- `Re ⟪W, A v⟫ ≥ c² ‖W‖² - ‖W‖ η'`
  have hinner : c ^ 2 * ‖W‖ ^ 2 - ‖W‖ * η' ≤ RCLike.re ⟪W, A v⟫_ℂ := by
    have hsplit : ⟪W, A v⟫_ℂ = ⟪W, T v⟫_ℂ + ⟪W, A v - T v⟫_ℂ := by
      rw [← inner_add_right, add_sub_cancel]
    have hTv' : RCLike.re ⟪W, T v⟫_ℂ = c ^ 2 * ‖W‖ ^ 2 := by
      have h : ⟪W, T v⟫_ℂ = ((c ^ 2 * ‖W‖ ^ 2 : ℝ) : ℂ) := by
        rw [hTv, inner_smul_right, inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
      rw [h, RCLike.re_to_complex, Complex.ofReal_re]
    have herr : -RCLike.re ⟪W, A v - T v⟫_ℂ ≤ ‖W‖ * ‖A v - T v‖ := by
      have hle := RCLike.re_le_norm (-⟪W, A v - T v⟫_ℂ)
      simp only [map_neg, norm_neg] at hle
      exact hle.trans (norm_inner_le_norm W _)
    have hlt : ‖W‖ * ‖A v - T v‖ ≤ ‖W‖ * η' := mul_le_mul_of_nonneg_left hFv.le (norm_nonneg W)
    rw [hsplit, map_add, hTv']
    linarith
  have hsq : ‖(ContinuousLinearMap.adjoint A - ContinuousLinearMap.adjoint T) W‖ ^ 2 < ε ^ 2 := by
    rw [BlockPropagatorSub.norm_adjoint_sub_sq_eq]
    have e1 : ‖ContinuousLinearMap.adjoint A W‖ ^ 2 ≤ (c + η) ^ 2 * ‖W‖ ^ 2 := by
      have h0 := norm_nonneg (ContinuousLinearMap.adjoint A W)
      calc ‖ContinuousLinearMap.adjoint A W‖ ^ 2 ≤ ((c + η) * ‖W‖) ^ 2 := pow_le_pow_left₀ h0 hAW 2
        _ = (c + η) ^ 2 * ‖W‖ ^ 2 := by ring
    have hηle1 : η ≤ 1 := min_le_left _ _
    have hηle2 : η ≤ ε ^ 2 / (4 * (2 * CB + 1) * Nw ^ 2) := min_le_right _ _
    have hk : (2 * CB + 1) * η * Nw ^ 2 ≤ ε ^ 2 / 4 := by
      calc (2 * CB + 1) * η * Nw ^ 2
          ≤ (2 * CB + 1) * (ε ^ 2 / (4 * (2 * CB + 1) * Nw ^ 2)) * Nw ^ 2 := by gcongr
        _ = ε ^ 2 / 4 := by field_simp
    have hWN : ‖W‖ ≤ Nw := by linarith
    have hW2 : ‖W‖ ^ 2 ≤ Nw ^ 2 := pow_le_pow_left₀ (norm_nonneg W) hWN 2
    have e3 : (2 * c * η + η ^ 2) * ‖W‖ ^ 2 ≤ ε ^ 2 / 4 := by
      have hq : 2 * c * η + η ^ 2 ≤ (2 * CB + 1) * η := by nlinarith
      calc (2 * c * η + η ^ 2) * ‖W‖ ^ 2 ≤ (2 * CB + 1) * η * ‖W‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hq (by positivity)
        _ ≤ (2 * CB + 1) * η * Nw ^ 2 := mul_le_mul_of_nonneg_left hW2 (by positivity)
        _ ≤ ε ^ 2 / 4 := hk
    have e4 : 2 * (‖W‖ * η') ≤ ε ^ 2 / 2 := by
      have h5 : ‖W‖ * η' ≤ Nw * η' := mul_le_mul_of_nonneg_right hWN hη'0.le
      have h6 : Nw * η' = ε ^ 2 / 4 := by rw [hη'def]; field_simp
      linarith
    have hε2 : 0 < ε ^ 2 := by positivity
    have e1' : ‖ContinuousLinearMap.adjoint A W‖ ^ 2 ≤
        c ^ 2 * ‖W‖ ^ 2 + (2 * c * η + η ^ 2) * ‖W‖ ^ 2 := by
      calc ‖ContinuousLinearMap.adjoint A W‖ ^ 2 ≤ (c + η) ^ 2 * ‖W‖ ^ 2 := e1
        _ = c ^ 2 * ‖W‖ ^ 2 + (2 * c * η + η ^ 2) * ‖W‖ ^ 2 := by ring
    have hv_sq' : ‖ContinuousLinearMap.adjoint T W‖ ^ 2 = c ^ 2 * ‖W‖ ^ 2 := hv_sq
    linarith [hinner, hv_sq', e1', e3, e4]
  have hlt := lt_of_pow_lt_pow_left₀ 2 hε.le hsq
  rwa [sub_apply] at hlt

/-- **Corrected target from the two leaves** (SP 2962-2972). -/
theorem relStrongLimitRe_of (κ : PlanarFrameKernels)
    (hD : RelFreeTestLimitTo κ planarRelTransportRe) (hN : RelFreeNormLimit κ) :
    RelStrongLimitRe κ :=
  relStrongLimitTo_of κ isRelLimitFamily_planarRelTransportRe hD hN

/-- The target `RelStrongLimit` (now with the real-damped limit) from the two leaves. -/
theorem relStrongLimit_of (κ : PlanarFrameKernels)
    (hD : RelFreeTestLimitTo κ planarRelTransportRe) (hN : RelFreeNormLimit κ) :
    RelStrongLimit κ :=
  relStrongLimitRe_of κ hD hN

end StrongA

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
