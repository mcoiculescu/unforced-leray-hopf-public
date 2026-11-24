import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.GraphAllP
import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Trunc
import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Dense
import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.IBP

/-!
# Part II-a, `PartII-a:F14/1/1/org`: `D2CoreDense` from the truncated resolvent and cutoffs

Source of record: `the November 2 reference manuscript`, lines 1456-1467 (the core
of `D_r`), with the inverse integral of lines 1370-1376 and the graph estimate of lemma
`bg:common-body-graph` (lines 1356-1366; proof 1426-1443).

Proof of `d2CoreDense_of` (all at `r = 2`, `μ = 1`, so `a_2 = 5/4`):

1. Let `f = (1+L)w ∈ Y_2` and choose phase tests `φ_n → f` in `Y_2` (`PhaseTestsDenseY2`, "approximate
   the right side by smooth periodic Schwartz functions").
2. Truncate the inverse integral at `M = n`: `Ψ_n = truncRes ν 1 n φ_n` is Schwartz-type
   (`TruncResSchwartz`), lies in `D_2` with its classical drift and diffusion (`SchwartzGraphIBP`), and
   `(1+L)Ψ_n = φ_n - e^{-n}S(n)φ_n(· - n)` (`TruncResEquation`). The remainder has `Y_2` norm
   `≤ e^{-5n/4}‖φ_n‖ → 0` (`FwdRemainderBound`), so `(1+L)Ψ_n → f`.
3. The graph estimate (`bodyGraphBoundAllP`, proved in `Sub/F14_1_org/GraphAllP.lean`) applied to
   `Ψ_n - w` gives graph convergence `Ψ_n → w` ("the graph estimate gives graph convergence of the
   truncations").
4. Radial cutoffs `χ_k Ψ_n` (`tendsto_cut`, `tendsto_cut_driftT`, `tendsto_cut_lapT` of
   `Lib/PhaseSpace/ExtendedTest.lean`: the drift commutator `½ (y·∇χ_k)` is bounded and supported on
   an escaping annulus, the diffusion commutators `2∇χ_k·∇ + Δχ_k` tend to zero) are phase tests
   converging to `Ψ_n` in the graph (`schwartz_triple_mem_closure`). The graph triple of `w` lies in
   the closure of the phase-test triples; a sequence realising it is the conclusion.

Proved in the helper folder `Sub/F14_1_org/`: `bodyGraphBoundAllP` (`GraphAllP.lean`),
`phaseTestsDenseY2` (`Dense.lean`), `schwartzGraphIBP` (`IBP.lean`), `fwdIntegrandCont`,
`truncResSchwartz_of`, `truncResEquation_of` (`Trunc.lean`). The open leaves are the four `Prop`s
of `d2CoreDense_of_leaves`: `FwdIntegrandRegular`, `FwdIntegrandDeriv`, `FwdIntegrandDecay`
(forward analogues of the proved `AdjIntegrandRegular`, `AdjIntegrandDeriv`, `AdjIntegrandDecay`),
and `FwdRemainderBound` (decomposed further through `FwdSliceL2` and `HeatGaussL2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-! ### `𝒯₀` and `νΔ` of slice tests -/

section SliceOps

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

omit [Fact (0 < P)] in
theorem isSliceTest_sub' {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ)
    (hΨ : IsSliceTest P r Ψ) : IsSliceTest P r (Φ - Ψ) := by
  have h : Φ - Ψ = Φ + (-1 : ℂ) • Ψ := by
    funext p
    simp [sub_eq_add_neg]
  rw [h]
  exact hΦ.add (hΨ.const_smul _)

theorem smul_half_complex (x : CVec3) : (1 / 2 : ℂ) • x = (1 / 2 : ℝ) • x := by
  rw [← Complex.coe_smul]
  norm_num

/-- `𝒯₀ = -𝒯₀ᵗ + 3/2` on smooth fields (`B0005.driftT_eq_neg_T0op`). -/
theorem T0op_eq_driftT (Φ : ℝ × Space → CVec3) :
    B0005.T0op Φ = -driftT Φ + (3 / 2 : ℂ) • Φ := by
  funext p
  have h32 : (3 / 2 : ℂ) • Φ p = (3 / 2 : ℝ) • Φ p := by
    rw [← Complex.coe_smul]
    norm_num
  simp only [B0005.T0op, driftT, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, h32]
  abel

theorem nuLapT_eq_smul (ν : ℝ) (Φ : ℝ × Space → CVec3) : nuLapT ν Φ = (ν : ℂ) • lapT Φ := by
  funext p
  simp [nuLapT, Complex.coe_smul]

theorem isSliceTest_T0op {Φ : ℝ × Space → CVec3} (h1 : IsSliceTest P r Φ)
    (h2 : IsSliceTest P r (driftT Φ)) : IsSliceTest P r (B0005.T0op Φ) := by
  rw [T0op_eq_driftT]
  exact h2.neg.add (h1.const_smul _)

omit [Fact (0 < P)] in
theorem isSliceTest_nuLapT {Φ : ℝ × Space → CVec3} (h : IsSliceTest P r (lapT Φ)) (ν : ℝ) :
    IsSliceTest P r (nuLapT ν Φ) := by
  rw [nuLapT_eq_smul]
  exact h.const_smul _

theorem testElem_sub' {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ)
    (hΨ : IsSliceTest P r Ψ) : testElem P r (Φ - Ψ) = testElem P r Φ - testElem P r Ψ := by
  have h : Φ - Ψ = Φ + (-1 : ℂ) • Ψ := by
    funext p
    simp [sub_eq_add_neg]
  rw [h, testElem_add hΦ (hΨ.const_smul _), testElem_const_smul hΨ, neg_one_smul,
    ← sub_eq_add_neg]

theorem testElem_T0op {Φ : ℝ × Space → CVec3} (h1 : IsSliceTest P r Φ)
    (h2 : IsSliceTest P r (driftT Φ)) :
    testElem P r (B0005.T0op Φ) = -testElem P r (driftT Φ) + (3 / 2 : ℂ) • testElem P r Φ := by
  rw [T0op_eq_driftT, testElem_add h2.neg (h1.const_smul _), testElem_neg h2,
    testElem_const_smul h1]

theorem testElem_nuLapT {Φ : ℝ × Space → CVec3} (h : IsSliceTest P r (lapT Φ)) (ν : ℝ) :
    testElem P r (nuLapT ν Φ) = (ν : ℂ) • testElem P r (lapT Φ) := by
  rw [nuLapT_eq_smul, testElem_const_smul h]

end SliceOps

/-! ### Radial cutoffs of a Schwartz-type function (lines 1465-1467) -/

/-- **Radial cutoffs approximate the Schwartz class in the graph** (lines 1465-1467): the graph
triple of a Schwartz-type `Ψ` is a limit of graph triples of phase tests (the cutoffs `χ_k Ψ`). -/
theorem schwartz_triple_mem_closure {P : ℝ} [Fact (0 < P)] (ν : ℝ) {Ψ : ℝ × Space → CVec3}
    (hΨ : IsPhaseSchwartz P 2 Ψ) :
    (testElem P 2 Ψ, testElem P 2 (B0005.T0op Ψ), testElem P 2 (nuLapT ν Ψ)) ∈
      closure {x : Yq P 2 × Yq P 2 × Yq P 2 | ∃ G : ℝ × Space → CVec3, IsPhaseTest P G ∧
        x = (testElem P 2 G, testElem P 2 (B0005.T0op G), testElem P 2 (nuLapT ν G))} := by
  have hr : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hG : ∀ k : ℕ, IsPhaseTest P (mulT (cutχ k) Ψ) := hΨ.isPhaseTest_cut
  have t1 : Tendsto (fun k : ℕ => testElem P 2 (mulT (cutχ k) Ψ)) atTop
      (𝓝 (testElem P 2 Ψ)) := tendsto_cut hr hΨ
  have t2 : Tendsto (fun k : ℕ => testElem P 2 (B0005.T0op (mulT (cutχ k) Ψ))) atTop
      (𝓝 (testElem P 2 (B0005.T0op Ψ))) := by
    have e : ∀ k : ℕ, testElem P 2 (B0005.T0op (mulT (cutχ k) Ψ)) =
        -testElem P 2 (driftT (mulT (cutχ k) Ψ)) + (3 / 2 : ℂ) • testElem P 2 (mulT (cutχ k) Ψ) :=
      fun k => testElem_T0op ((hG k).isSliceTest 2) ((hG k).driftT.isSliceTest 2)
    rw [testElem_T0op hΨ.sliceTest hΨ.sliceTest_driftT]
    simp only [e]
    exact (tendsto_cut_driftT hr hΨ).neg.add (t1.const_smul _)
  have t3 : Tendsto (fun k : ℕ => testElem P 2 (nuLapT ν (mulT (cutχ k) Ψ))) atTop
      (𝓝 (testElem P 2 (nuLapT ν Ψ))) := by
    have e : ∀ k : ℕ, testElem P 2 (nuLapT ν (mulT (cutχ k) Ψ)) =
        (ν : ℂ) • testElem P 2 (lapT (mulT (cutχ k) Ψ)) :=
      fun k => testElem_nuLapT ((hG k).lapT.isSliceTest 2) ν
    rw [testElem_nuLapT hΨ.sliceTest_lapT ν]
    simp only [e]
    exact (tendsto_cut_lapT hr hΨ).const_smul _
  exact mem_closure_of_tendsto (t1.prodMk_nhds (t2.prodMk_nhds t3))
    (Eventually.of_forall fun k => ⟨mulT (cutχ k) Ψ, hG k, rfl⟩)

/-! ### One truncation in the graph (lines 1456-1463) -/

/-- **A truncated inverse integral of a phase test lies in `D_2`**, with its classical drift and
diffusion, and `(1 + L)` of it is the right side minus the remainder (lines 1456-1462). -/
theorem truncRes_graph (hS : TruncResSchwartz) (hE : TruncResEquation) (hR : FwdRemainderBound)
    (hI : SchwartzGraphIBP) {P : ℝ} [Fact (0 < P)] {ν : ℝ} (hν : 0 < ν)
    {f : ℝ × Space → CVec3} (hf : IsPhaseTest P f) {M : ℝ} (hM : 0 ≤ M) :
    ∃ hw : testElem P 2 (truncRes ν 1 M f) ∈ D P ν 2,
      T0D (⟨_, hw⟩ : D P ν 2) = testElem P 2 (B0005.T0op (truncRes ν 1 M f)) ∧
      nuLapD (⟨_, hw⟩ : D P ν 2) = testElem P 2 (nuLapT ν (truncRes ν 1 M f)) ∧
      bodyOp P ν 2 1 ⟨_, hw⟩ = testElem P 2 f - testElem P 2 (fwdIntegrand ν 1 f M) := by
  have hP : 0 < P := Fact.out
  have hs : IsPhaseSchwartz P 2 (truncRes ν 1 M f) := hS P ν hP hν 1 f hf M hM
  obtain ⟨hIL, hIT⟩ := hI P 2 ν (truncRes ν 1 M f) hs
  have hw : testElem P 2 (truncRes ν 1 M f) ∈ D P ν 2 := mem_D.2 ⟨⟨_, hIL⟩, ⟨_, hIT⟩⟩
  have hT : T0D (⟨_, hw⟩ : D P ν 2) = testElem P 2 (B0005.T0op (truncRes ν 1 M f)) :=
    T0D_eq hIT
  have hL : nuLapD (⟨_, hw⟩ : D P ν 2) = testElem P 2 (nuLapT ν (truncRes ν 1 M f)) :=
    nuLapD_eq hIL
  refine ⟨hw, hT, hL, ?_⟩
  have h1 : IsSliceTest P 2 (truncRes ν 1 M f) := hs.sliceTest
  have hT' : IsSliceTest P 2 (B0005.T0op (truncRes ν 1 M f)) :=
    isSliceTest_T0op hs.sliceTest hs.sliceTest_driftT
  have hL' : IsSliceTest P 2 (nuLapT ν (truncRes ν 1 M f)) :=
    isSliceTest_nuLapT hs.sliceTest_lapT ν
  have hrem : IsSliceTest P 2 (fwdIntegrand ν 1 f M) := (hR P ν hν 1 f hf M hM).1
  have hfun : truncRes ν 1 M f + (B0005.T0op (truncRes ν 1 M f) - nuLapT ν (truncRes ν 1 M f) -
      (1 / 2 : ℂ) • truncRes ν 1 M f) = f - fwdIntegrand ν 1 f M := by
    funext p
    have h := hE P ν hP hν 1 f hf M hM p
    simp only [one_smul, L0, T0] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, B0005.T0op, nuLapT, smul_half_complex]
    exact h
  have e1 : bodyOp P ν 2 1 ⟨_, hw⟩ = testElem P 2 (truncRes ν 1 M f) +
      (T0D (⟨_, hw⟩ : D P ν 2) - nuLapD (⟨_, hw⟩ : D P ν 2) -
        (1 / 2 : ℂ) • testElem P 2 (truncRes ν 1 M f)) := by
    show (1 : ℂ) • testElem P 2 (truncRes ν 1 M f) + L0D (⟨_, hw⟩ : D P ν 2) = _
    rw [one_smul]
    rfl
  rw [e1, hT, hL, ← testElem_const_smul h1, ← testElem_sub' hT' hL',
    ← testElem_sub' (isSliceTest_sub' hT' hL') (h1.const_smul _),
    ← testElem_add h1 (isSliceTest_sub' (isSliceTest_sub' hT' hL') (h1.const_smul _)), hfun,
    testElem_sub' (hf.isSliceTest 2) hrem]

/-! ### The composition -/

/-- **`D2CoreDense` from the leaves** (lines 1456-1467): the phase tests are a core of the maximal
graph `D_2`, for every period `P > 0`. -/
theorem d2CoreDense_of (hS : TruncResSchwartz) (hE : TruncResEquation) (hR : FwdRemainderBound)
    (hD : PhaseTestsDenseY2) (hI : SchwartzGraphIBP) : D2CoreDense := by
  intro P _ ν hν w
  obtain ⟨C, hC0, hCb⟩ := bodyGraphBoundAllP 2 ENNReal.one_lt_two (by norm_num)
  have hγ : gammaR 2 = 1 / 4 := by
    simp only [gammaR, ENNReal.toReal_ofNat]; norm_num
  have hμ1 : 0 < (1 : ℂ).re + gammaR 2 := by rw [hγ]; norm_num
  obtain ⟨φ, hφ, hφf⟩ := hD P (bodyOp P ν 2 1 w)
  choose hmem hT hL hB using fun n : ℕ =>
    truncRes_graph hS hE hR hI hν (hφ n) (Nat.cast_nonneg (α := ℝ) n)
  obtain ⟨v, hv⟩ : ∃ v : ℕ → D P ν 2, ∀ n : ℕ,
      (v n : Yq P 2) = testElem P 2 (truncRes ν 1 n (φ n)) ∧
      T0D (v n) = testElem P 2 (B0005.T0op (truncRes ν 1 n (φ n))) ∧
      nuLapD (v n) = testElem P 2 (nuLapT ν (truncRes ν 1 n (φ n))) ∧
      bodyOp P ν 2 1 (v n) = testElem P 2 (φ n) - testElem P 2 (fwdIntegrand ν 1 (φ n) n) :=
    ⟨fun n => ⟨_, hmem n⟩, fun n => ⟨rfl, hT n, hL n, hB n⟩⟩
  -- the remainder tends to zero (line 1463)
  have hrem : Tendsto (fun n : ℕ => testElem P 2 (fwdIntegrand ν 1 (φ n) n)) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, ‖testElem P 2 (fwdIntegrand ν 1 (φ n) n)‖ ≤
        Real.exp (-((1 : ℂ).re + 1 / 4) * n) * ‖testElem P 2 (φ n)‖ :=
      fun n => (hR P ν hν 1 (φ n) (hφ n) n (Nat.cast_nonneg n)).2
    have hlin : Tendsto (fun n : ℕ => -((1 : ℂ).re + 1 / 4) * (n : ℝ)) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_natCast_atTop_atTop
    have hexp : Tendsto (fun n : ℕ => Real.exp (-((1 : ℂ).re + 1 / 4) * n)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hlin
    have hprod : Tendsto (fun n : ℕ => Real.exp (-((1 : ℂ).re + 1 / 4) * n) *
        ‖testElem P 2 (φ n)‖) atTop (𝓝 0) := by
      have := hexp.mul ((continuous_norm.tendsto _).comp hφf)
      simpa using this
    exact squeeze_zero_norm hb hprod
  -- `(1 + L)(v_n - w) → 0`
  have hdiff : Tendsto (fun n => bodyOp P ν 2 1 (v n - w)) atTop (𝓝 0) := by
    have e : ∀ n : ℕ, bodyOp P ν 2 1 (v n - w) =
        (testElem P 2 (φ n) - bodyOp P ν 2 1 w) - testElem P 2 (fwdIntegrand ν 1 (φ n) n) := by
      intro n
      rw [map_sub, (hv n).2.2.2]
      abel
    simp only [e]
    have h1 : Tendsto (fun n => testElem P 2 (φ n) - bodyOp P ν 2 1 w) atTop (𝓝 0) := by
      have := hφf.sub_const (bodyOp P ν 2 1 w)
      simpa using this
    simpa using h1.sub hrem
  -- the graph estimate gives graph convergence (line 1463-1464)
  have hgn : Tendsto (fun n => graphNormD (v n - w)) atTop (𝓝 0) := by
    have hle : ∀ n, graphNormD (v n - w) ≤
        C * (1 + (1 + ‖(1 : ℂ)‖) / ((1 : ℂ).re + gammaR 2)) * ‖bodyOp P ν 2 1 (v n - w)‖ :=
      fun n => hCb P ν hν 1 hμ1 (v n - w)
    have h0 : ∀ n, 0 ≤ graphNormD (v n - w) := fun n => by
      unfold graphNormD; positivity
    have hK : Tendsto (fun n => C * (1 + (1 + ‖(1 : ℂ)‖) / ((1 : ℂ).re + gammaR 2)) *
        ‖bodyOp P ν 2 1 (v n - w)‖) atTop (𝓝 0) := by
      have := hdiff.norm.const_mul (C * (1 + (1 + ‖(1 : ℂ)‖) / ((1 : ℂ).re + gammaR 2)))
      simpa using this
    exact squeeze_zero h0 hle hK
  have hsubT : ∀ n, T0D (v n - w) = T0D (v n) - T0D w := fun n => by
    have := map_sub (T0L (P := P) (ν := ν) (q := 2)) (v n) w
    simpa only [T0L_apply] using this
  have hsubL : ∀ n, nuLapD (v n - w) = nuLapD (v n) - nuLapD w := fun n => by
    have := map_sub (nuLapL (P := P) (ν := ν) (q := 2)) (v n) w
    simpa only [nuLapL_apply] using this
  have c1 : Tendsto (fun n => (v n : Yq P 2)) atTop (𝓝 (w : Yq P 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgn
    have e : ((v n - w : D P ν 2) : Yq P 2) = (v n : Yq P 2) - (w : Yq P 2) := rfl
    have := norm_nonneg (nuLapD (v n - w))
    have := norm_nonneg (T0D (v n - w))
    unfold graphNormD
    rw [e]
    linarith
  have c2 : Tendsto (fun n => T0D (v n)) atTop (𝓝 (T0D w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgn
    have := norm_nonneg ((v n - w : D P ν 2) : Yq P 2)
    have := norm_nonneg (nuLapD (v n - w))
    unfold graphNormD
    rw [hsubT n]
    linarith
  have c3 : Tendsto (fun n => nuLapD (v n)) atTop (𝓝 (nuLapD w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgn
    have := norm_nonneg ((v n - w : D P ν 2) : Yq P 2)
    have := norm_nonneg (T0D (v n - w))
    unfold graphNormD
    rw [hsubL n]
    linarith
  -- the graph triple of `w` is in the closure of the phase-test triples
  have hwcl : ((w : Yq P 2), T0D w, nuLapD w) ∈
      closure {x : Yq P 2 × Yq P 2 × Yq P 2 | ∃ G : ℝ × Space → CVec3, IsPhaseTest P G ∧
        x = (testElem P 2 G, testElem P 2 (B0005.T0op G), testElem P 2 (nuLapT ν G))} := by
    refine isClosed_closure.mem_of_tendsto (c1.prodMk_nhds (c2.prodMk_nhds c3))
      (Eventually.of_forall fun n => ?_)
    rw [(hv n).1, (hv n).2.1, (hv n).2.2.1]
    exact schwartz_triple_mem_closure ν
      (hS P ν (Fact.out) hν 1 (φ n) (hφ n) n (Nat.cast_nonneg n))
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.1 hwcl
  choose G hG hGx using hxS
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · have := (continuous_fst.tendsto _).comp hx
    simpa [Function.comp_def, hGx] using this
  · have := ((continuous_fst.comp continuous_snd).tendsto _).comp hx
    simpa [Function.comp_def, hGx] using this
  · have := ((continuous_snd.comp continuous_snd).tendsto _).comp hx
    simpa [Function.comp_def, hGx] using this

/-- **`D2CoreDense` from the four open leaves** (everything else is proved in `Sub/F14_1_org/`). -/
theorem d2CoreDense_of_leaves (h1 : FwdIntegrandRegular) (h2 : FwdIntegrandDeriv)
    (h3 : FwdIntegrandDecay) (h4 : FwdRemainderBound) : D2CoreDense :=
  d2CoreDense_of (truncResSchwartz_of h1 h3) (truncResEquation_of h1 h2 fwdIntegrandCont) h4
    phaseTestsDenseY2 schwartzGraphIBP

end UnforcedLeray.Short.PartIIa
