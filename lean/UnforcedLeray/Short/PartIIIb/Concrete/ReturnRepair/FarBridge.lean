import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The far bridge: from the box pin of `S_far` to every source (organizer `ORG:C-review/far-bridge`)

Source of record `the November 2 reference manuscript` (73 pages):
3593-3594 ("we begin with smooth tensors and then complete in the norms appearing below"),
3611-3621 (`sep:resolvent`), 3902-3912 (`S_far = 1_{s<S, t>e^δs}S_ε`, "the notation for the mask
means its exact kernel realization with tensor partitions before distributional divergence"),
4171 and 4203-4214 (`W_μ = -S_μ(χ_oT)`, the young-old rectangle), 5301-5372 (the far mask
`s < S`, `t > e^δs`, `S = ε^{-b}`; its early-source and late-output regions and the transition
table), 5569-5605 (the velocity bounds of the same regions), 5687-5689 (the decomposition of
`S_far T + Y[T]`).

The operators of `Concrete/ReturnInst.lean` are `Classical.epsilon` of their pins, and the far part
`S_far = Sop - SNop` (`SopSubIsFarSeq`, `IsNearSplit`) is pinned by `IsFarMaskG` only on stresses
whose component sum is a box tensor (`NearInst.IsBoxTensor`): there `S_far F = farOut f`
(`NearInst.Masked.farOut`, the masked `sep:resolvent` response read at the receiver).  Every
region estimate of the age error (5301-5372, 5569-5605) is a kernel bound proved for `farOut` of
box tensors and must be completed to all sources (3593-3594).  This file does that completion
ONCE, for an arbitrary bounded `Sf` with the pin, and for every region:

* **Truncation** (`trunc`, `win`, `tendsto_trunc`, `strSum_trunc_of`, `win_box`, `farBoxTrunc`):
  `1_{W_k}T → T` in the split stress space for the windows
  `W_k = {1/(k+1) ≤ s ≤ k, |η| ≤ k, ‖f‖ ≤ k}` of a measurable representative `f` of `T₁ + T₂`
  (`NearInst.Masked.bdWin`), whose component sums are the box tensors `1_{W_k}f`.
  `farBoxTrunc` is `StrBoxTrunc` (`EarlyRepThin/Kernel/Bridge.lean`) verbatim.
* **Closed receivers** (`RecvClosed`, `FatouAE`): a receiver functional `N` passes to limits if its
  sublevel sets are sequentially closed; this holds for continuous `N` (`RecvClosed.of_continuous`,
  e.g. `‖Φ v‖` for a continuous linear `Φ`) and for the ungained Lebesgue norms of a continuous
  `Lp`-valued map, by an a.e. subsequence and Fatou (`RecvClosed.lp`, `fatouAE_lintegral`,
  `fatouAE_eLpNorm`, `RecvClosed.lintegral_comp`, `RecvClosed.eLpNorm_comp`): `z1Ung`, `htUng`,
  `hTUng`, `velBin`, `eLpNorm _ 2 (srcMeasure c)` of `(M_U Sf T)_{1,2}` or of `Sf T`.
* **The bridge in bound form** (`farBridge_le`, `farBridge_le_mono`; pure density `le_of_win`):
  `N(Sf T) ≤ M` for every stress `T` with measurable representative `f` of `T₁ + T₂` as soon as
  `N v ≤ M` for every `v` a.e. equal to `farOut(1_W f)` with `1_W f` a box tensor (only the
  truncations of `f` are needed, so support conditions of a region, e.g. the early source
  `(1-χ_o)T₂` or the old source `χ_oT`, pass to the box tensors).  With a source functional `Q`
  that does not increase under truncation (`phaseL2Lr_indicator_le`, `lintegral_indicator_le`)
  this is `farBridge_le_mono`.  Output regions (late output `(1-χ_y)`, young receiver `χ_y`) enter
  through `N` (e.g. `N v = ‖Φ ((1 - χ_y) v)‖`), source regions through `T` and `f`.
* **The bridge as an identity** (`farBridge_ae_of`): `Sf T = farOut f` a.e. on every output set
  `O` on which the order-zero gap majorant `IIIa.sepDom` of the lifted source is finite (the
  absolute convergence of the masked `sep:resolvent` integral, gap `(1-e^{-δ/2})R/√s`); the
  dominated-convergence step through the `(λ, z)` integral is the leaf `FarOutTruncTendsto`
  (task `ORG:C-review/far-bridge/1`).  Applied on the young receiver `νs ≤ 1` with the old source
  `χ_oT` (ages `t ≥ 1.2/ν > e^δ s`), where the mask is inactive, it reads `S_far(χ_oT)` as the
  separated response `-W_μ` of 4171; with `χ_yS_Nχ_o = 0` (`nearYoungOld`) this is the young-old
  rectangle of `S_far T + Y[T]` (5303-5306, 5687-5689).  The rectangle cancels only in that sum:
  nothing here bounds `S_far` or `Y` alone on it.

No receiver needed by the region estimates is a phase norm of a physical lift (`phaseL2Lr`,
`phaseSupLr`, `IIIa.ltauLq ∘ velPhys`): the region kernels convert to chart norms on box tensors
first (e.g. `FarUngRecvConv`), so the Fatou forms above are on chart `Lp` norms; the source side
`phaseL2Lr` only needs monotonicity under truncation (`phaseL2Lr_indicator_le`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarBridge

/-! ## 1. Closed receivers -/

/-- **Sequentially closed sublevel sets** of a receiver functional: a uniform bound along a
convergent sequence passes to the limit. -/
def RecvClosed {E : Type*} [TopologicalSpace E] (N : E → ℝ≥0∞) : Prop :=
  ∀ (vs : ℕ → E) (v : E) (M : ℝ≥0∞), Tendsto vs atTop (𝓝 v) → (∀ k, N (vs k) ≤ M) → N v ≤ M

theorem RecvClosed.of_continuous {E : Type*} [TopologicalSpace E] {N : E → ℝ≥0∞}
    (hN : Continuous N) : RecvClosed N := by
  intro vs v M hv hM
  exact le_of_tendsto' ((hN.tendsto v).comp hv) hM

theorem RecvClosed.comp {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {N : F → ℝ≥0∞} (hN : RecvClosed N) {g : E → F} (hg : Continuous g) :
    RecvClosed (fun x => N (g x)) := by
  intro vs v M hv hM
  exact hN (fun k => g (vs k)) (g v) M ((hg.tendsto v).comp hv) hM

/-- `‖Φ v‖` for a continuous `Φ` (e.g. `(·)₁ ∘ M_U ∘ χ_y`, the receiver of `EarlyFarSepBridge`). -/
theorem RecvClosed.ofReal_norm {E F : Type*} [TopologicalSpace E] [SeminormedAddCommGroup F]
    {Φ : E → F} (hΦ : Continuous Φ) : RecvClosed (fun v => ENNReal.ofReal ‖Φ v‖) :=
  RecvClosed.of_continuous (ENNReal.continuous_ofReal.comp (continuous_norm.comp hΦ))

/-- **Fatou along `μ'`-a.e. convergence**: a functional of functions whose sublevel sets are
closed under a.e. limits of a.e. strongly measurable sequences. -/
def FatouAE {α E : Type*} [MeasurableSpace α] [TopologicalSpace E] (μ' : Measure α)
    (F : (α → E) → ℝ≥0∞) : Prop :=
  ∀ (gs : ℕ → α → E) (g : α → E) (M : ℝ≥0∞), (∀ k, AEStronglyMeasurable (gs k) μ') →
    (∀ᵐ x ∂μ', Tendsto (fun k => gs k x) atTop (𝓝 (g x))) → (∀ k, F (gs k) ≤ M) → F g ≤ M

/-- **`Lp` convergence and Fatou**: an `Lp`-convergent sequence has an a.e. convergent
subsequence. -/
theorem RecvClosed.lp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {μ' : Measure α} {F : (α → E) → ℝ≥0∞} (hF : FatouAE μ' F) :
    RecvClosed (fun u : Lp E p μ' => F u) := by
  intro us u M hu hM
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  exact hF (fun i => us (ns i)) u M (fun i => Lp.aestronglyMeasurable _) hae (fun i => hM (ns i))

/-- **Fatou for `(∫ ‖g‖^q dμ'')^{1/q}`**, `μ'' ≪ μ'` (the ungained norms `z1Ung`, `htUng`,
`hTUng`, `velBin` are of this form with `q = 2`). -/
theorem fatouAE_lintegral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ' μ'' : Measure α} (hac : μ'' ≪ μ') {q : ℝ} (hq : 0 < q) :
    FatouAE μ' (fun g : α → E => (∫⁻ x, ‖g x‖ₑ ^ q ∂μ'') ^ (1 / q)) := by
  intro gs g M hmeas hae hM
  have hae' : ∀ᵐ x ∂μ'', Tendsto (fun k => ‖gs k x‖ₑ ^ q) atTop (𝓝 (‖g x‖ₑ ^ q)) := by
    filter_upwards [hac.ae_le hae] with x hx
    exact ((ENNReal.continuous_rpow_const).tendsto _).comp ((continuous_enorm.tendsto _).comp hx)
  have hle : ∀ k, ∫⁻ x, ‖gs k x‖ₑ ^ q ∂μ'' ≤ M ^ q := by
    intro k
    have h := ENNReal.rpow_le_rpow (hM k) hq.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one] at h
  have hmeas' : ∀ k, AEMeasurable (fun x => ‖gs k x‖ₑ ^ q) μ'' := fun k =>
    ((hmeas k).mono_ac hac).enorm.pow_const q
  have hfat : ∫⁻ x, ‖g x‖ₑ ^ q ∂μ'' ≤ M ^ q := by
    calc ∫⁻ x, ‖g x‖ₑ ^ q ∂μ''
        = ∫⁻ x, liminf (fun k => ‖gs k x‖ₑ ^ q) atTop ∂μ'' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae'] with x hx
          exact hx.liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ x, ‖gs k x‖ₑ ^ q ∂μ'') atTop := lintegral_liminf_le' hmeas'
      _ ≤ M ^ q := liminf_le_of_frequently_le' (Frequently.of_forall hle)
  calc (∫⁻ x, ‖g x‖ₑ ^ q ∂μ'') ^ (1 / q) ≤ (M ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hfat (by positivity)
    _ = M := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- **Fatou for `eLpNorm _ p μ''`**, `μ'' ≪ μ'`, `0 < p < ∞`. -/
theorem fatouAE_eLpNorm {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ' μ'' : Measure α} (hac : μ'' ≪ μ') {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    FatouAE μ' (fun g : α → E => eLpNorm g p μ'') := by
  intro gs g M hmeas hae hM
  have h := fatouAE_lintegral (E := E) hac (ENNReal.toReal_pos hp0 hpt) gs g M hmeas hae
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt] at hM ⊢
  exact h hM

/-- The ungained `(∫ ‖g X‖^q dμ'')^{1/q}` of a continuous `Lp`-valued map is closed. -/
theorem RecvClosed.lintegral_comp {E α F : Type*} [TopologicalSpace E] [MeasurableSpace α]
    [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ' μ'' : Measure α} (hac : μ'' ≪ μ')
    {q : ℝ} (hq : 0 < q) {g : E → Lp F p μ'} (hg : Continuous g) :
    RecvClosed (fun X => (∫⁻ x, ‖(g X : α → F) x‖ₑ ^ q ∂μ'') ^ (1 / q)) :=
  (RecvClosed.lp (fatouAE_lintegral (E := F) hac hq)).comp hg

/-- `eLpNorm (g X) p' μ''` of a continuous `Lp`-valued map is closed. -/
theorem RecvClosed.eLpNorm_comp {E α F : Type*} [TopologicalSpace E] [MeasurableSpace α]
    [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ' μ'' : Measure α} (hac : μ'' ≪ μ')
    {p' : ℝ≥0∞} (hp0 : p' ≠ 0) (hpt : p' ≠ ∞) {g : E → Lp F p μ'} (hg : Continuous g) :
    RecvClosed (fun X => eLpNorm (g X : α → F) p' μ'') :=
  (RecvClosed.lp (fatouAE_eLpNorm (E := F) hac hp0 hpt)).comp hg

/-- The component maps of the split stress space are continuous. -/
theorem continuous_strFst {c mZ ρb γ ν : ℝ} :
    Continuous fun x : StrG c mZ ρb γ ν => x.fst :=
  (ContinuousLinearMap.fst ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).continuous.comp
    (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
      (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).continuous

theorem continuous_strSnd {c mZ ρb γ ν : ℝ} :
    Continuous fun x : StrG c mZ ρb γ ν => x.snd :=
  (ContinuousLinearMap.snd ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).continuous.comp
    (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
      (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).continuous

/-! ## 2. Truncation of a stress -/

section Trunc

variable {c mZ ρb γ ν : ℝ}

/-- The truncated stress `1_W T = (1_W T₁, 1_W T₂)`. -/
def trunc (T : StrG c mZ ρb γ ν) {W : Set Chart} (hW : MeasurableSet W) : StrG c mZ ρb γ ν :=
  WithLp.toLp 1 (((Lp.memLp T.fst).indicator hW).toLp (W.indicator (T.fst : Chart → Ten3)),
    ((Lp.memLp T.snd).indicator hW).toLp (W.indicator (T.snd : Chart → Ten3)))

theorem trunc_fst (T : StrG c mZ ρb γ ν) {W : Set Chart} (hW : MeasurableSet W) :
    (trunc T hW).fst =
      ((Lp.memLp T.fst).indicator hW).toLp (W.indicator (T.fst : Chart → Ten3)) := rfl

theorem trunc_snd (T : StrG c mZ ρb γ ν) {W : Set Chart} (hW : MeasurableSet W) :
    (trunc T hW).snd =
      ((Lp.memLp T.snd).indicator hW).toLp (W.indicator (T.snd : Chart → Ten3)) := rfl

theorem trunc_fst_ae (T : StrG c mZ ρb γ ν) {W : Set Chart} (hW : MeasurableSet W) :
    ((trunc T hW).fst : Chart → Ten3) =ᵐ[ageμ c (-1 / 2)] W.indicator (T.fst : Chart → Ten3) := by
  have hl : MemLp (W.indicator (T.fst : Chart → Ten3)) 2 (gainZ1Measure c mZ γ ν) :=
    (Lp.memLp T.fst).indicator hW
  have h := hl.coeFn_toLp
  rw [Filter.EventuallyEq, NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h
  rw [trunc_fst]
  exact h

theorem trunc_snd_ae (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) {W : Set Chart}
    (hW : MeasurableSet W) :
    ((trunc T hW).snd : Chart → Ten3) =ᵐ[ageμ c (-1 / 2)] W.indicator (T.snd : Chart → Ten3) := by
  have hl : MemLp (W.indicator (T.snd : Chart → Ten3)) 2 (gainHTMeasure c ρb γ ν) :=
    (Lp.memLp T.snd).indicator hW
  have h := hl.coeFn_toLp
  rw [Filter.EventuallyEq, NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h
  rw [trunc_snd]
  exact h

/-- The component sum of the truncation is the truncated component sum. -/
theorem strSum_trunc (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) {W : Set Chart}
    (hW : MeasurableSet W) :
    strSum (trunc T hW) =ᵐ[ageμ c (-1 / 2)] W.indicator (strSum T) := by
  filter_upwards [trunc_fst_ae T hW, trunc_snd_ae hρ T hW] with p a b
  simp only [strSum]
  rw [a, b]
  by_cases hp : p ∈ W
  · simp [Set.indicator_of_mem hp, strSum]
  · simp [Set.indicator_of_notMem hp]

theorem strSum_trunc_of (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) {W : Set Chart}
    (hW : MeasurableSet W) {f : Chart → Ten3} (hTf : strSum T =ᵐ[ageμ c (-1 / 2)] f) :
    strSum (trunc T hW) =ᵐ[ageμ c (-1 / 2)] W.indicator f := by
  filter_upwards [strSum_trunc hρ T hW, hTf] with p h1 h2
  rw [h1]
  by_cases hp : p ∈ W
  · simp [Set.indicator_of_mem hp, h2]
  · simp [Set.indicator_of_notMem hp]

/-- The thin source `(T₁, 0)` has component sum `T₁` a.e. -/
theorem strSum_thinPart (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) :
    strSum (thinPart T) =ᵐ[ageμ c (-1 / 2)] (T.fst : Chart → Ten3) := by
  have h0 : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), ((thinPart T).snd : Chart → Ten3) p = 0 := by
    have e : (thinPart T).snd = 0 := by simp [thinPart]
    rw [e]
    exact Lp.coeFn_zero _ _ _
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h0
  have e1 : (thinPart T).fst = T.fst := by simp [thinPart]
  filter_upwards [h0] with p hp
  simp only [strSum, hp, add_zero, e1]

/-- The repair source `(0, T₂)` has component sum `T₂` a.e. -/
theorem strSum_repPart (T : StrG c mZ ρb γ ν) :
    strSum (repPart T) =ᵐ[ageμ c (-1 / 2)] (T.snd : Chart → Ten3) := by
  have h0 : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ((repPart T).fst : Chart → Ten3) p = 0 := by
    have e : (repPart T).fst = 0 := by simp [repPart]
    rw [e]
    exact Lp.coeFn_zero _ _ _
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h0
  have e2 : (repPart T).snd = T.snd := by simp [repPart]
  filter_upwards [h0] with p hp
  simp only [strSum, hp, zero_add, e2]

/-- The repair source of a truncation: `strSum (0, (1_W T)₂) = 1_W T₂` a.e. -/
theorem strSum_repPart_trunc (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) {W : Set Chart}
    (hW : MeasurableSet W) :
    strSum (repPart (trunc T hW)) =ᵐ[ageμ c (-1 / 2)] W.indicator (T.snd : Chart → Ten3) := by
  have h0 : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν),
      ((repPart (trunc T hW)).fst : Chart → Ten3) p = 0 := by
    have e : (repPart (trunc T hW)).fst = 0 := by simp [repPart]
    rw [e]
    exact Lp.coeFn_zero _ _ _
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h0
  have e2 : (repPart (trunc T hW)).snd = (trunc T hW).snd := by simp [repPart]
  filter_upwards [h0, trunc_snd_ae hρ T hW] with p hp hs
  simp only [strSum, hp, zero_add, e2]
  exact hs

/-- The thin source of a truncation: `strSum ((1_W T)₁, 0) = 1_W T₁` a.e. -/
theorem strSum_thinPart_trunc (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) {W : Set Chart}
    (hW : MeasurableSet W) :
    strSum (thinPart (trunc T hW)) =ᵐ[ageμ c (-1 / 2)] W.indicator (T.fst : Chart → Ten3) := by
  have h0 : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν),
      ((thinPart (trunc T hW)).snd : Chart → Ten3) p = 0 := by
    have e : (thinPart (trunc T hW)).snd = 0 := by simp [thinPart]
    rw [e]
    exact Lp.coeFn_zero _ _ _
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h0
  have e1 : (thinPart (trunc T hW)).fst = (trunc T hW).fst := by simp [thinPart]
  filter_upwards [h0, trunc_fst_ae T hW] with p hp hs
  simp only [strSum, hp, add_zero, e1]
  exact hs

/-- `‖u - 1_W u‖ = ‖1_{Wᶜ} u‖`. -/
theorem norm_sub_toLp_indicator {μ' : Measure Chart} (u : Lp (α := Chart) Ten3 2 μ')
    {W : Set Chart} (hW : MeasurableSet W) :
    ‖u - ((Lp.memLp u).indicator hW).toLp (W.indicator (u : Chart → Ten3))‖ =
      (eLpNorm (Wᶜ.indicator (u : Chart → Ten3)) 2 μ').toReal := by
  rw [Lp.norm_def]
  have h1 : eLpNorm (⇑(u - ((Lp.memLp u).indicator hW).toLp (W.indicator (u : Chart → Ten3))))
      2 μ' = eLpNorm ((u : Chart → Ten3) - W.indicator (u : Chart → Ten3)) 2 μ' :=
    eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
      (EventuallyEq.sub EventuallyEq.rfl (MemLp.coeFn_toLp _)))
  have h2 : (u : Chart → Ten3) - W.indicator (u : Chart → Ten3) =
      Wᶜ.indicator (u : Chart → Ten3) := by
    funext p
    by_cases h : p ∈ W
    · simp [Set.indicator_of_mem h, Set.indicator_of_notMem (show p ∉ Wᶜ from fun h' => h' h)]
    · simp [Set.indicator_of_notMem h, Set.indicator_of_mem (show p ∈ Wᶜ from h)]
  rw [h1, h2]

theorem tendsto_cut_toReal {μ' : Measure Chart} (u : Lp (α := Chart) Ten3 2 μ')
    {W : ℕ → Set Chart} (hW : ∀ k, MeasurableSet (W k)) (hmono : Monotone W)
    (hcov : ∀ᵐ p ∂μ', ∃ k, p ∈ W k) :
    Tendsto (fun k => (eLpNorm ((W k)ᶜ.indicator (u : Chart → Ten3)) 2 μ').toReal) atTop
      (𝓝 0) := by
  have h := NearInst.Masked.bd_tendsto_cut (Lp.stronglyMeasurable u).measurable (Lp.memLp u)
    W hW hmono hcov
  have h0 : (0 : ℝ) = (0 : ℝ≥0∞).toReal := rfl
  rw [h0]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- **Truncations converge** in the split stress space, for windows exhausting `s > 0`. -/
theorem tendsto_trunc (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) {W : ℕ → Set Chart}
    (hW : ∀ k, MeasurableSet (W k)) (hmono : Monotone W)
    (hcov : ∀ p : Chart, 0 < p.1 → ∃ k, p ∈ W k) :
    Tendsto (fun k => trunc T (hW k)) atTop (𝓝 T) := by
  have pos : ∀ᵐ p ∂(ageμ c (-1 / 2)), ∃ k, p ∈ W k := by
    filter_upwards [UnforcedLeray.Short.IIIa.ae_pos_ageμ c (-1 / 2)] with p hp using hcov p hp
  have cov1 : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ∃ k, p ∈ W k := by
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure]; exact pos
  have cov2 : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), ∃ k, p ∈ W k := by
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ]; exact pos
  have t1 := tendsto_cut_toReal T.fst hW hmono cov1
  have t2 := tendsto_cut_toReal T.snd hW hmono cov2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ k, ‖trunc T (hW k) - T‖ =
      (eLpNorm ((W k)ᶜ.indicator (T.fst : Chart → Ten3)) 2 (gainZ1Measure c mZ γ ν)).toReal +
        (eLpNorm ((W k)ᶜ.indicator (T.snd : Chart → Ten3)) 2 (gainHTMeasure c ρb γ ν)).toReal := by
    intro k
    rw [norm_sub_rev, WithLp.prod_norm_eq_of_L1]
    change ‖T.fst - ((Lp.memLp T.fst).indicator (hW k)).toLp _‖ +
      ‖T.snd - ((Lp.memLp T.snd).indicator (hW k)).toLp _‖ = _
    rw [norm_sub_toLp_indicator _ (hW k), norm_sub_toLp_indicator _ (hW k)]
  simp only [e]
  simpa using t1.add t2

/-! ### The windows of a representative -/

/-- The window `W_k = {1/(k+1) ≤ s ≤ k, |η| ≤ k, ‖f‖ ≤ k}` (`NearInst.Masked.bdWin f f k`). -/
def win (f : Chart → Ten3) (k : ℕ) : Set Chart := NearInst.Masked.bdWin f f k

theorem win_meas {f : Chart → Ten3} (hf : Measurable f) (k : ℕ) : MeasurableSet (win f k) :=
  NearInst.Masked.bdWin_meas hf hf k

theorem win_mono (f : Chart → Ten3) : Monotone (win f) := NearInst.Masked.bdWin_mono f f

theorem win_cover (f : Chart → Ten3) {p : Chart} (hp : 0 < p.1) : ∃ k, p ∈ win f k :=
  NearInst.Masked.bdWin_cover f f hp

/-- `1_{W_k} f` is a box tensor. -/
theorem win_box {f : Chart → Ten3} (hf : Measurable f) (k : ℕ) :
    NearInst.IsBoxTensor ((win f k).indicator f) := by
  refine ⟨hf.indicator (win_meas hf k), ⟨k, fun p => ?_⟩,
    ⟨1 / ((k : ℝ) + 1), k, k, by positivity, fun p hp => ?_⟩⟩
  · by_cases hpW : p ∈ win f k
    · rw [Set.indicator_of_mem hpW]
      exact hpW.2.2.2.1
    · rw [Set.indicator_of_notMem hpW, norm_zero]
      positivity
  · by_cases hpW : p ∈ win f k
    · exact ⟨hpW.1, hpW.2.1, hpW.2.2.1⟩
    · exact absurd (Set.indicator_of_notMem hpW f) hp

theorem tendsto_trunc_win (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) {f : Chart → Ten3}
    (hf : Measurable f) : Tendsto (fun k => trunc T (win_meas hf k)) atTop (𝓝 T) :=
  tendsto_trunc hρ T (win_meas hf) (win_mono f) (fun _ hp => win_cover f hp)

end Trunc

/-- **Box truncation of a stress** (3593-3594, 3905-3912; the statement `StrBoxTrunc` of
`EarlyRepThin/Kernel/Bridge.lean` verbatim). -/
theorem farBoxTrunc (c mZ ρb γ ν : ℝ) (_hc : 0 < c) (hρ : 0 < ρb) (_hν : 0 < ν)
    (F : StrG c mZ ρb γ ν) (f : Chart → Ten3) (hf : Measurable f)
    (hFf : strSum F =ᵐ[ageμ c (-1 / 2)] f) :
    ∃ (A : ℕ → Set Chart) (Fn : ℕ → StrG c mZ ρb γ ν),
      (∀ k, NearInst.IsBoxTensor ((A k).indicator f)) ∧
      (∀ k, strSum (Fn k) =ᵐ[ageμ c (-1 / 2)] (A k).indicator f) ∧
      Tendsto Fn atTop (𝓝 F) :=
  ⟨win f, fun k => trunc F (win_meas hf k), win_box hf,
    fun k => strSum_trunc_of hρ F (win_meas hf k) hFf, tendsto_trunc_win hρ F hf⟩

/-! ## 3. The bridge in bound form -/

section Bound

variable {c mZ ρb γ ν : ℝ}

/-- **Density** (3593-3594): a closed functional bounded on the window truncations of `T` is
bounded at `T`. -/
theorem le_of_win (hρ : 0 < ρb) {Φ : StrG c mZ ρb γ ν → ℝ≥0∞} (hΦ : RecvClosed Φ)
    (T : StrG c mZ ρb γ ν) {f : Chart → Ten3} (hf : Measurable f) {M : ℝ≥0∞}
    (h : ∀ k, Φ (trunc T (win_meas hf k)) ≤ M) : Φ T ≤ M :=
  hΦ _ T M (tendsto_trunc_win hρ T hf) h

/-- **The far bridge** (3593-3594, 3902-3912): for `Sf` with the box pin `IsFarMaskG`, every
closed receiver bound valid on the far-kernel outputs `farOut (1_W f)` of the box truncations of
a representative `f` of `T₁ + T₂` holds for `Sf T`. -/
theorem farBridge_le (hρ : 0 < ρb) {R μ δ Scut : ℝ}
    {Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν} (hSf : IsFarMaskG R μ δ Scut Sf)
    {N : VelG c γ ν → ℝ≥0∞} (hN : RecvClosed N) {T : StrG c mZ ρb γ ν} {f : Chart → Ten3}
    (hf : Measurable f) (hTf : strSum T =ᵐ[ageμ c (-1 / 2)] f) {M : ℝ≥0∞}
    (h : ∀ (W : Set Chart) (v : VelG c γ ν), MeasurableSet W →
      NearInst.IsBoxTensor (W.indicator f) →
      (v : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
        NearInst.Masked.farOut R c ν μ δ Scut (W.indicator f) → N v ≤ M) :
    N (Sf T) ≤ M := by
  refine le_of_win hρ (Φ := fun X => N (Sf X)) (hN.comp Sf.continuous) T hf (fun k => ?_)
  exact h _ _ (win_meas hf k) (win_box hf k)
    (hSf _ _ (win_box hf k) (strSum_trunc_of hρ T (win_meas hf k) hTf))

/-- **The far bridge with a monotone source norm**: a box bound `N v ≤ B·Q g` for `v = farOut g`
passes to `N(Sf T) ≤ B·Q f` when `Q` does not increase under truncation of `f`. -/
theorem farBridge_le_mono (hρ : 0 < ρb) {R μ δ Scut : ℝ}
    {Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν} (hSf : IsFarMaskG R μ δ Scut Sf)
    {N : VelG c γ ν → ℝ≥0∞} (hN : RecvClosed N) {T : StrG c mZ ρb γ ν} {f : Chart → Ten3}
    (hf : Measurable f) (hTf : strSum T =ᵐ[ageμ c (-1 / 2)] f)
    {Q : (Chart → Ten3) → ℝ≥0∞} (hQ : ∀ W : Set Chart, MeasurableSet W → Q (W.indicator f) ≤ Q f)
    {B : ℝ≥0∞}
    (h : ∀ (v : VelG c γ ν) (g : Chart → Ten3), NearInst.IsBoxTensor g →
      (v : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] NearInst.Masked.farOut R c ν μ δ Scut g →
      N v ≤ B * Q g) :
    N (Sf T) ≤ B * Q f :=
  farBridge_le hρ hSf hN hf hTf fun W v hW hb hv =>
    (h v _ hb hv).trans (mul_le_mul_of_nonneg_left (hQ W hW) zero_le)

end Bound

/-! ## 4. Source norms that do not increase under truncation -/

open Classical in
theorem cartLift_indicator (R c : ℝ) (W : Set Chart) (f : Chart → Ten3) (τ : ℝ) (z : Space) :
    NearInst.cartLift R c (W.indicator f) τ z =
      if NearInst.chartOf R c z τ ∈ W then NearInst.cartLift R c f τ z else 0 := by
  have h0 : NearInst.nsSym (0 : Ten3) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ]
  by_cases h : NearInst.chartOf R c z τ ∈ W
  · rw [if_pos h]
    simp only [NearInst.cartLift, Set.indicator_of_mem h]
  · rw [if_neg h]
    simp only [NearInst.cartLift, Set.indicator_of_notMem h, h0, smul_zero, Matrix.mul_zero,
      Matrix.zero_mul]

theorem tensorNorm_strPhys_indicator_le (R c : ℝ) (W : Set Chart) (f : Chart → Ten3)
    (x : ℝ × Space) :
    UnforcedLeray.Short.IIIa.tensorNorm (strPhys R c (W.indicator f) x) ≤
      UnforcedLeray.Short.IIIa.tensorNorm (strPhys R c f x) := by
  unfold strPhys
  rw [cartLift_indicator]
  split_ifs
  · exact le_rfl
  · have h0 : UnforcedLeray.Short.IIIa.tensorNorm (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      simp [UnforcedLeray.Short.IIIa.tensorNorm]
    rw [h0]
    exact Real.sqrt_nonneg _

/-- `‖𝒩_T(1_W f)‖_{L²_τL^r} ≤ ‖𝒩_T f‖_{L²_τL^r}`, `r > 0`. -/
theorem phaseL2Lr_indicator_le (P r R c : ℝ) (hr : 0 < r) (W : Set Chart) (f : Chart → Ten3) :
    phaseL2Lr P r (strPhys R c (W.indicator f)) ≤ phaseL2Lr P r (strPhys R c f) := by
  unfold phaseL2Lr
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine mul_le_mul_of_nonneg_left (lintegral_mono fun t => ?_) zero_le
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  refine lintegral_mono fun y => ?_
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (tensorNorm_strPhys_indicator_le R c W f _)) hr.le

/-- `(∫ ‖1_W f‖^q)^{1/q} ≤ (∫ ‖f‖^q)^{1/q}`, `q > 0` (`z1Ung`, `htUng`, `hTUng`, `z1Part`). -/
theorem lintegral_indicator_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ' : Measure α) {q : ℝ} (hq : 0 < q) (W : Set α) (f : α → E) :
    (∫⁻ x, ‖W.indicator f x‖ₑ ^ q ∂μ') ^ (1 / q) ≤ (∫⁻ x, ‖f x‖ₑ ^ q ∂μ') ^ (1 / q) := by
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by positivity)
  refine ENNReal.rpow_le_rpow ?_ hq.le
  by_cases h : x ∈ W
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, enorm_zero]
    exact zero_le

/-! ## 5. The bridge as an a.e. identity -/

/-- **Dominated convergence through the masked `sep:resolvent` integral** (3604-3621 with
`sep:kernel` `|∇K_t(x)| ≤ C|x|^{-4}`; 3905-3912 the mask `t > e^δs`, i.e. `|z'| < e^{-δ/2}R/√s`,
so `|y - λz| ≥ (1-e^{-δ/2})R/√s` at the receiver `y = chartY R x`, `|y'| = R/√s`): at an output
point `x` of age `s = x.1 > 0` at which the order-zero gap majorant `IIIa.sepDom` of the lifted
source is finite, the far outputs of the truncations `1_{W_k}f` converge to that of `f`, for
measurable windows increasing to `{s > 0}`.  (Pointwise `cartLift (1_{W_k}f) → cartLift f`, since
the lift reads `f` at the single chart point `chartOf`, of age `R²/|z'|² > 0` off the axis; the
masked integrand is dominated by `C λ^{2μ+2} 1_{|y-λz| ≥ D}|y-λz|^{-4}|𝒩_Tf(τ+2log λ, z)|`.) -/
def FarOutTruncTendsto : Prop :=
  ∀ (R c ν μ δ S : ℝ), 0 < R → 0 < c → 0 < ν → -(1 / 4) < μ → 0 < δ →
    ∀ f : Chart → Ten3, Measurable f →
    ∀ W : ℕ → Set Chart, (∀ k, MeasurableSet (W k)) → Monotone W →
      (∀ p : Chart, 0 < p.1 → ∃ k, p ∈ W k) →
    ∀ x : Chart, 0 < x.1 →
      UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
          ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt x.1)
          (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))
          (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤ →
      Tendsto (fun k => NearInst.Masked.farOut R c ν μ δ S ((W k).indicator f) x) atTop
        (𝓝 (NearInst.Masked.farOut R c ν μ δ S f x))

/-- **The far bridge as an identity** (3593-3594, 3611-3621, 3902-3912): for `Sf` with the box pin
`IsFarMaskG` and every stress `T` with measurable representative `f` of `T₁ + T₂`,
`Sf T = farOut f` a.e. on every output set `O` on which the order-zero gap majorant of the lifted
source is finite (absolute convergence of the masked kernel integral).  Proof: the window
truncations converge (`tendsto_trunc_win`), `Sf` is continuous, an a.e. subsequence, the pin on each
truncation and `FarOutTruncTendsto` at the output point. -/
theorem farBridge_ae_of (hD : FarOutTruncTendsto) {c mZ ρb γ ν R μ δ Scut : ℝ} (hR : 0 < R)
    (hc : 0 < c) (hρ : 0 < ρb) (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hδ : 0 < δ)
    {Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν} (hSf : IsFarMaskG R μ δ Scut Sf)
    {T : StrG c mZ ρb γ ν} {f : Chart → Ten3} (hf : Measurable f)
    (hTf : strSum T =ᵐ[ageμ c (-1 / 2)] f) {O : Set Chart}
    (habs : ∀ᵐ x ∂(ageμ c (-3 / 2)), x ∈ O →
      UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
          ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt x.1)
          (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))
          (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤) :
    ∀ᵐ x ∂(ageμ c (-3 / 2)), x ∈ O →
      (Sf T : Chart → Merid) x = NearInst.Masked.farOut R c ν μ δ Scut f x := by
  have hlimV : Tendsto (fun k => Sf (trunc T (win_meas hf k))) atTop (𝓝 (Sf T)) :=
    (Sf.continuous.tendsto T).comp (tendsto_trunc_win hρ T hf)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlimV).exists_seq_tendsto_ae
  rw [NearInst.ae_bodyMeasure] at hae
  have hpin : ∀ᵐ x ∂(ageμ c (-3 / 2)), ∀ k,
      (Sf (trunc T (win_meas hf k)) : Chart → Merid) x =
        NearInst.Masked.farOut R c ν μ δ Scut ((win f k).indicator f) x := by
    rw [ae_all_iff]
    intro k
    exact hSf _ _ (win_box hf k) (strSum_trunc_of hρ T (win_meas hf k) hTf)
  filter_upwards [hae, hpin, habs, UnforcedLeray.Short.IIIa.ae_pos_ageμ c (-3 / 2)] with
    x hx hp habx hpos hxO
  have h1 : Tendsto (fun i => NearInst.Masked.farOut R c ν μ δ Scut ((win f (ns i)).indicator f) x)
      atTop (𝓝 ((Sf T : Chart → Merid) x)) :=
    hx.congr fun i => hp (ns i)
  have h2 := hD R c ν μ δ Scut hR hc hν hμ hδ f hf (win f) (win_meas hf) (win_mono f)
    (fun p hp => win_cover f hp) x hpos (habx hxO)
  exact tendsto_nhds_unique h1 (h2.comp hns.tendsto_atTop)

end UnforcedLeray.Short.PartIIIb.Concrete.FarBridge
