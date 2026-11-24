import UnforcedLeray.Blueprint.Localization.Linear
import UnforcedLeray.Infra.WeaklyNullCompact
import UnforcedLeray.Infra.VolterraEvolution.Kernel
import UnforcedLeray.Units.B0418.Operator

/-!
# L5, abstract part: from the compact Duhamel kernel to the Calkin bound

`paper/main.tex` lines 331–347 (blueprint units B0714 (d), B0715). This file proves, for the
blueprint's step data (`IsCoefficients`, `IsFreeEvolution`, `IsEvolution` of
`Blueprint/Localization/Linear.lean`):

* `X_ext_of_ae`: an element of `X = H¹_div` is determined by its value;
* `S0_comp_S0`, `S0L_add`: the semigroup laws of the free evolution `S₀`, read off the literal
  formula `S₀(s)f(y) = e^{s/2}[e^{h(e^s-1)Δ}f](e^{s/2}y)` (the semigroup law of that formula is
  `Units/B0418/Semigroup.lean`, `freeEvolution_add`);
* `monodromy_pow`: `𝓜ⁿ = E(n𝒯, 0)` (evolution law and periodicity, B0715 infrastructure);
* `tendsto_E_sub_S0_of_weaklyNull`: on a strip `s ≤ τ ≤ s + 1`, `(E(τ,s) - S₀(τ-s))xₙ → 0` for
  every weakly null `xₙ`, provided each `S₀(t)𝓑_*(r)`, `0 < t ≤ 1`, maps weakly null sequences
  to null sequences (`DuhamelKernelNull`); dominated convergence in the Duhamel integral of
  `IsEvolution.duhamel` with the integrable bound `C (τ-r)^{-1/2}` (lines 336–340). Adapted
  from `Infra/CompactDuhamel/Strip.lean`, which states the same for `VolterraData`;
* `isCompactOperator_E_sub_S0`: `E(τ,s) - S₀(τ-s)` is compact for all `s ≤ τ` (lines 338–340),
  by the weakly-null criterion (`Infra/WeaklyNullCompact.lean`) on strips and induction over
  strips as in `Infra/CompactDuhamel/Global.lean`;
* `calkinBound_of_duhamelKernelNull`: `CalkinBound 𝓜 𝒯` (lines 340–343), with the compact
  operator `E(n𝒯,0) - S₀(n𝒯)` and `‖S₀(n𝒯)‖ ≤ C e^{-n𝒯/4}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace UnforcedLeray.Loc.L05

open UnforcedLeray.Blueprint UnforcedLeray.Infra.WeaklyNullCompact

/-! ## `X` and the free evolution -/

/-- An element of `X = H¹_div` is determined by its value (weak derivatives are unique). -/
theorem X_ext_of_ae {f g : X} (h : Xval f =ᵐ[volume] Xval g) : f = g := by
  have h1 : Xclass f = Xclass g := Lp.ext h
  have h2 : f.toH1 = g.toH1 := SobolevGraph.H1.value_injective h1
  exact Subtype.ext h2

theorem norm_L2div (F : L2div) : ‖F‖ = ‖Lclass F‖ := rfl

theorem norm_ιX (f : X) : ‖ιX f‖ = ‖Xclass f‖ := rfl

theorem toL2_Lval (F : L2div) : toL2 (Lval F) = Lclass F :=
  ViscosityTransport.toL2_coe (Lclass F)

variable {h : ℝ} {S : FreeEvolution}

/-- The semigroup law `S₀(a)S₀(b) = S₀(a+b)` on `X` (`loc:eq:free-evolution`, line 292). -/
theorem S0_comp_S0 (hh : 0 ≤ h) (hS : IsFreeEvolution h S) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : (S.S0 a).comp (S.S0 b) = S.S0 (a + b) := by
  refine ContinuousLinearMap.ext fun f => X_ext_of_ae ?_
  rw [ContinuousLinearMap.comp_apply]
  have h1 := hS.rep a ha (S.S0 b f)
  have h3 := B0418.freeEvolution_congr_ae (hS.rep b hb f) h a
  have h4 : AncientLocalization.freeEvolution h a (AncientLocalization.freeEvolution h b (Xval f)) =
      AncientLocalization.freeEvolution h (a + b) (Xval f) :=
    B0418.freeEvolution_add (p := 2) hh ha hb one_le_two (by norm_num) (Lp.memLp _)
  rw [h4] at h3
  exact h1.trans (h3.trans (hS.rep (a + b) (add_nonneg ha hb) f).symm)

/-- The smoothing semigroup law `S₀(a+b) = S₀(a) ι S₀(b)` from `L²_div` to `X`. -/
theorem S0L_add (hh : 0 ≤ h) (hS : IsFreeEvolution h S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (F : L2div) : S.S0L (a + b) F = S.S0L a (ιX (S.S0L b F)) := by
  apply X_ext_of_ae
  have h1 := hS.repL a ha (ιX (S.S0L b F))
  rw [Lval_ιX] at h1
  have h3 := B0418.freeEvolution_congr_ae (hS.repL b hb F) h a
  have h4 : AncientLocalization.freeEvolution h a (AncientLocalization.freeEvolution h b (Lval F)) =
      AncientLocalization.freeEvolution h (a + b) (Lval F) :=
    B0418.freeEvolution_add (p := 2) hh ha.le hb.le one_le_two (by norm_num) (Lp.memLp _)
  rw [h4] at h3
  exact (hS.repL (a + b) (add_pos ha hb) F).trans (h3.symm.trans h1.symm)

/-- The `L²` norm of `S₀(b)F` is `e^{-b/4}` times the heat norm at time `h(e^b-1)`. -/
theorem norm_ιX_S0L (hS : IsFreeEvolution h S) {b : ℝ} (hb : 0 < b) (F : L2div) :
    ‖ιX (S.S0L b F)‖ =
      Real.exp (-b / 4) * ‖Heat.heatOperator (h * (Real.exp b - 1)) (Lclass F)‖ := by
  rw [norm_ιX, Lp.norm_def]
  have hc := eLpNorm_congr_ae (p := 2) (hS.repL b hb F)
  change (eLpNorm (Xval (S.S0L b F)) 2 volume).toReal = _
  rw [hc]
  have hmem : MemLp (Lval F) 2 volume := Lp.memLp _
  have := AncientLocalization.freeEvolution_l2Norm_eq hmem h b
  unfold l2Norm at this
  rw [this]
  congr 1
  rw [← toL2_Lval, ← Heat.toL2_flow hmem, norm_toL2 (Heat.flow_memLp hmem _)]
  rfl

/-! ## Weakly null sequences -/

/-- A weakly null sequence in `X`. -/
def WeaklyNull (x : ℕ → X) : Prop := ∀ y : X, Tendsto (fun n => ⟪y, x n⟫_ℝ) atTop (𝓝 0)

theorem weaklyNull_map (T : X →L[ℝ] X) {x : ℕ → X} (hx : WeaklyNull x) :
    WeaklyNull (fun n => T (x n)) := by
  have h := ((weakTendsto_zero_iff (𝕜 := ℝ)).mpr hx).map T
  rw [map_zero] at h
  exact (weakTendsto_zero_iff (𝕜 := ℝ)).mp h

/-- The compactness input of lines 333–336: `S₀(t)𝓑_*(r) : X → X` maps weakly null sequences
to null sequences for `0 < t ≤ 1` (equivalently, it is compact). -/
def DuhamelKernelNull (c : Coefficients) (S : FreeEvolution) : Prop :=
  ∀ t r : ℝ, 0 < t → t ≤ 1 → ∀ x : ℕ → X, WeaklyNull x →
    Tendsto (fun n => S.S0L t (c.B r (x n))) atTop (𝓝 0)

/-! ## Compactness of `E(τ,s) - S₀(τ-s)` -/

variable {D : BackgroundData} {c : Coefficients} {ev : Evolution}

/-- Lines 336–340 on one strip: the Duhamel term maps weakly null sequences to null ones. -/
theorem tendsto_E_sub_S0_of_weaklyNull (hS : IsFreeEvolution D.h S) (hc : IsCoefficients D c)
    (hev : IsEvolution D c S ev) (hK : DuhamelKernelNull c S) {s τ : ℝ} (h1 : s ≤ τ)
    (h2 : τ ≤ s + 1) {x : ℕ → X} (hx : WeaklyNull x) :
    Tendsto (fun n => (ev.E τ s - S.S0 (τ - s)) (x n)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_norm_le_of_weaklyNull (𝕜 := ℝ) hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨C0, -, -, hC0L⟩ := hS.bounds
  obtain ⟨CE, hCE⟩ := hev.strip_bounds 1 one_pos
  obtain ⟨CB, hCB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.B_continuous.continuousOn (s := Icc s τ))
  have hrep : ∀ n, (ev.E τ s - S.S0 (τ - s)) (x n) =
      ∫ r in Ioo s τ, S.S0L (τ - r) (c.B r (ev.E r s (x n))) := by
    intro n
    show ev.E τ s (x n) - S.S0 (τ - s) (x n) = _
    rw [hev.duhamel s τ h1 (x n), add_sub_cancel_left]
  simp only [hrep]
  have h0 : (0 : X) = ∫ _ in Ioo s τ, (0 : X) := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence
    (fun r => C0 * (τ - r) ^ (-(1 / 2 : ℝ)) * (CB * (CE * M))) ?_ ?_ ?_ ?_
  · intro n
    exact (hev.duhamel_integrable s τ h1 (x n)).aestronglyMeasurable
  · have hk := Infra.VolterraEvolution.intervalIntegrable_kernel τ s τ
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le h1] at hk
    exact (hk.const_mul C0).mul_const _
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hpos : 0 < τ - r := by linarith [hr.2]
    have hle : τ - r ≤ 1 := by linarith [hr.1]
    have hB := hCB r ⟨hr.1.le, hr.2.le⟩
    have hCB0 : 0 ≤ CB := (norm_nonneg _).trans hB
    have hE := (hCE s r hr.1.le (by linarith [hr.2])).1
    have hCE0 : 0 ≤ CE := (norm_nonneg _).trans hE
    have hS0 := (hC0L (τ - r) hpos hle).1
    have hsq : C0 / Real.sqrt (τ - r) = C0 * (τ - r) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hpos.le, div_eq_mul_inv]
    rw [hsq] at hS0
    calc ‖S.S0L (τ - r) (c.B r (ev.E r s (x n)))‖
        ≤ ‖S.S0L (τ - r)‖ * (‖c.B r‖ * (‖ev.E r s‖ * ‖x n‖)) := by
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ C0 * (τ - r) ^ (-(1 / 2 : ℝ)) * (CB * (CE * M)) := by
          refine mul_le_mul hS0 ?_ (by positivity) ((norm_nonneg _).trans hS0)
          exact mul_le_mul hB (mul_le_mul hE (hM n) (norm_nonneg _) hCE0) (by positivity) hCB0
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hK (τ - r) r (by linarith [hr.2]) (by linarith [hr.1]) _
      (weaklyNull_map (ev.E r s) hx)

/-- `E(τ,s) - S₀(τ-s)` is compact on a strip `s ≤ τ ≤ s + 1`. -/
theorem isCompactOperator_E_sub_S0_strip (hS : IsFreeEvolution D.h S) (hc : IsCoefficients D c)
    (hev : IsEvolution D c S ev) (hK : DuhamelKernelNull c S) {s τ : ℝ} (h1 : s ≤ τ)
    (h2 : τ ≤ s + 1) : IsCompactOperator (ev.E τ s - S.S0 (τ - s)) :=
  isCompactOperator_of_forall_weaklyNull (𝕜 := ℝ) _ fun _ hx =>
    tendsto_zero_iff_norm_tendsto_zero.mp
      (tendsto_E_sub_S0_of_weaklyNull hS hc hev hK h1 h2 hx)

/-- **B0714 (d)** (lines 338–340): `E(τ,s) - S₀(τ-s)` is compact for every `s ≤ τ`. -/
theorem isCompactOperator_E_sub_S0 (hh : 0 ≤ D.h) (hS : IsFreeEvolution D.h S)
    (hc : IsCoefficients D c) (hev : IsEvolution D c S ev) (hK : DuhamelKernelNull c S)
    {s τ : ℝ} (hsτ : s ≤ τ) : IsCompactOperator (ev.E τ s - S.S0 (τ - s)) := by
  suffices H : ∀ n : ℕ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + n + 1 →
      IsCompactOperator (ev.E τ s - S.S0 (τ - s)) by
    exact H ⌊τ - s⌋₊ s τ hsτ (by have := Nat.lt_floor_add_one (τ - s); linarith)
  intro n
  induction n with
  | zero =>
    intro s τ h1 h2
    exact isCompactOperator_E_sub_S0_strip hS hc hev hK h1 (by simpa using h2)
  | succ n ih =>
    intro s τ h1 h2
    by_cases h : τ ≤ s + 1
    · exact isCompactOperator_E_sub_S0_strip hS hc hev hK h1 h
    · rw [not_le] at h
      have hK1 := ih (s + 1) τ h.le (by push_cast at h2; linarith)
      have hK2 := isCompactOperator_E_sub_S0_strip hS hc hev hK (s := s) (τ := s + 1)
        (by linarith) le_rfl
      have heq : ev.E τ s - S.S0 (τ - s) =
          (ev.E τ (s + 1) - S.S0 (τ - (s + 1))).comp (ev.E (s + 1) s) +
            (S.S0 (τ - (s + 1))).comp (ev.E (s + 1) s - S.S0 (s + 1 - s)) := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
          hev.law s (s + 1) τ (by linarith) h.le,
          S0_comp_S0 hh hS (by linarith) (by linarith)]
        have : τ - (s + 1) + (s + 1 - s) = τ - s := by ring
        rw [this]
        abel
      rw [heq]
      exact (hK1.comp_clm _).add (hK2.clm_comp _)

/-- `𝓜ⁿ = E(n𝒯, 0)`, from the evolution law and periodicity (B0715). -/
theorem monodromy_pow (hev : IsEvolution D c S ev) (hP : 0 ≤ D.period) (n : ℕ) :
    monodromy D ev ^ n = ev.E (n * D.period) 0 := by
  induction n with
  | zero => simp [hev.at_diag, ContinuousLinearMap.one_def]
  | succ n ih =>
    rw [pow_succ, ih, ContinuousLinearMap.mul_def, monodromy]
    have hlaw := hev.law 0 D.period ((n + 1 : ℕ) * D.period) hP
      (by push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have hper := hev.periodic (n * D.period) 0
    rw [zero_add] at hper
    rw [← hlaw]
    congr 1
    rw [← hper]
    congr 1
    push_cast
    ring

/-- **B0715** (lines 340–343): the Calkin bound `‖π(𝓜ⁿ)‖ ≤ C e^{-n𝒯/4}`, in real form, from
the compactness input `DuhamelKernelNull`. -/
theorem calkinBound_of_duhamelKernelNull (hh : 0 ≤ D.h) (hP : 0 ≤ D.period)
    (hS : IsFreeEvolution D.h S) (hc : IsCoefficients D c) (hev : IsEvolution D c S ev)
    (hK : DuhamelKernelNull c S) : CalkinBound (monodromy D ev) D.period := by
  obtain ⟨C, -, hdecay, -⟩ := hS.bounds
  refine ⟨C, fun n => ⟨ev.E (n * D.period) 0 - S.S0 (n * D.period - 0),
    isCompactOperator_E_sub_S0 hh hS hc hev hK (by positivity), ?_⟩⟩
  rw [monodromy_pow hev hP n, sub_sub_cancel, sub_zero]
  exact hdecay (n * D.period) (by positivity)

end UnforcedLeray.Loc.L05
