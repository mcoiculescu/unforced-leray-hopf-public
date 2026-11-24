import UnforcedLeray.Lib.PhaseSpace.Graph
import UnforcedLeray.Lib.PhaseSpace.Cutoff

/-!
# Extending tested identities to Schwartz-type phase tests (INF25 T25.3)

Scoping note `INF15-INF17-INF25-Parabolic.md` §5, target T25.3 (`HasPhaseOp.extend`), used by
the duality uniqueness of T25.4 (bypass B25-2) and the manuscript's graph arguments (B0411,
B0427, B0439, B0440; tex 7304–7337, 7540–7614). A distributional identity `L f = g` on `Y_q`
is defined by pairing with phase tests of bounded spatial support (`HasPhaseOp`). The
duality argument pairs with test functions that are smooth and periodic but only decay: the
adjoint resolvent of a test. `IsPhaseSchwartz P q' Ψ` records exactly what the extension
needs: `Ψ` smooth and `P`-periodic, and the slices of `Ψ`, `∂ⱼΨ`, `ΔΨ` and `T₀ᵗΨ` lying in
`L^{q'}(ℝ³)` and depending continuously on the phase there.

For `1 < q` (so `q' < ∞`) and `L ∈ {∂ⱼ, νΔ, T₀}` the identity extends:
`⟪Lᵗ Ψ, f⟫ = ⟪Ψ, g⟫` (`HasPhaseOp.extend_dy`, `extend_lap`, `extend_drift`).

Proof: `Ψₙ = χₙ Ψ` with the cutoffs `χₙ(y) = ψ(y/(n+1))` are phase tests. The commutators
`[Lᵗ, χₙ]` are multipliers that are bounded and tend to zero pointwise (`Cutoff.lean`), so
`Ψₙ → Ψ` and `Lᵗ Ψₙ → Lᵗ Ψ` in `Y_{q'}` (`Multiplier.lean`). The pairing is continuous on
`Y_{q'} × Y_q`, which passes the identity to the limit. Every phase test is phase-Schwartz
(`IsPhaseTest.isPhaseSchwartz`), so the extended identity contains the defining one.

Status: infrastructure only; no manuscript unit is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

/-- **Schwartz-type phase tests** (T25.3): smooth, `P`-periodic, with `Ψ`, `∂ⱼΨ`, `ΔΨ`,
`T₀ᵗΨ` slice-continuous into `L^r(ℝ³)`. -/
structure IsPhaseSchwartz (P : ℝ) (r : ℝ≥0∞) [Fact (1 ≤ r)] (Ψ : ℝ × Space → CVec3) :
    Prop where
  smooth : ContDiff ℝ ∞ Ψ
  periodic : ∀ τ y, Ψ (τ + P, y) = Ψ (τ, y)
  slice : SliceCont r Ψ
  slice_dy : ∀ j, SliceCont r (dy j Ψ)
  slice_lapT : SliceCont r (lapT Ψ)
  slice_driftT : SliceCont r (driftT Ψ)

/-- Every phase test is a Schwartz-type phase test. -/
theorem IsPhaseTest.isPhaseSchwartz {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] : IsPhaseSchwartz P r Φ :=
  ⟨hΦ.smooth, hΦ.periodic, hΦ.sliceCont r, fun j => (hΦ.dy j).sliceCont r,
    hΦ.lapT.sliceCont r, hΦ.driftT.sliceCont r⟩

/-! ### Periodicity of derivatives -/

section Per

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {P : ℝ}

theorem periodic_fderiv_apply {Φ : ℝ × Space → F} (h : ∀ τ y, Φ (τ + P, y) = Φ (τ, y))
    (v : ℝ × Space) : ∀ τ y, fderiv ℝ Φ (τ + P, y) v = fderiv ℝ Φ (τ, y) v := by
  intro τ y
  have hfun : (fun p : ℝ × Space => Φ (p + ((P : ℝ), (0 : Space)))) = Φ := by
    funext p
    obtain ⟨t, z⟩ := p
    simpa using h t z
  have h' := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ) (x := ((τ : ℝ), y)) ((P : ℝ), (0 : Space))
  rw [hfun] at h'
  have hp : ((τ, y) : ℝ × Space) + (P, 0) = (τ + P, y) := by simp
  rw [hp] at h'
  rw [← h']

theorem periodic_dy {Φ : ℝ × Space → F} (h : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)) (j : Fin 3) :
    ∀ τ y, dy j Φ (τ + P, y) = dy j Φ (τ, y) :=
  periodic_fderiv_apply h _

theorem periodic_dτ {Φ : ℝ × Space → F} (h : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)) :
    ∀ τ y, dτ Φ (τ + P, y) = dτ Φ (τ, y) :=
  periodic_fderiv_apply h _

theorem periodic_lapT {Φ : ℝ × Space → F} (h : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)) :
    ∀ τ y, lapT Φ (τ + P, y) = lapT Φ (τ, y) := by
  intro τ y
  simp only [lapT]
  exact Finset.sum_congr rfl fun j _ => periodic_dy (periodic_dy h j) j τ y

theorem periodic_driftT {Φ : ℝ × Space → F} (h : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)) :
    ∀ τ y, driftT Φ (τ + P, y) = driftT Φ (τ, y) := by
  intro τ y
  simp only [driftT, radialT, periodic_dτ h τ y, h τ y, periodic_dy h _ τ y]

end Per

namespace IsPhaseSchwartz

variable {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)] {Ψ : ℝ × Space → CVec3}

theorem sliceTest (hΨ : IsPhaseSchwartz P r Ψ) : IsSliceTest P r Ψ := ⟨hΨ.periodic, hΨ.slice⟩

theorem sliceTest_dy (hΨ : IsPhaseSchwartz P r Ψ) (j : Fin 3) : IsSliceTest P r (dy j Ψ) :=
  ⟨periodic_dy hΨ.periodic j, hΨ.slice_dy j⟩

theorem sliceTest_lapT (hΨ : IsPhaseSchwartz P r Ψ) : IsSliceTest P r (lapT Ψ) :=
  ⟨periodic_lapT hΨ.periodic, hΨ.slice_lapT⟩

theorem sliceTest_driftT (hΨ : IsPhaseSchwartz P r Ψ) : IsSliceTest P r (driftT Ψ) :=
  ⟨periodic_driftT hΨ.periodic, hΨ.slice_driftT⟩

/-- The cutoff approximants `χₙ Ψ` are phase tests. -/
theorem isPhaseTest_cut (hΨ : IsPhaseSchwartz P r Ψ) (n : ℕ) :
    IsPhaseTest P (mulT (cutχ n) Ψ) where
  smooth := contDiff_mulT (contDiff_cutχ n) hΨ.smooth
  periodic τ y := by simp [mulT, hΨ.periodic τ y]
  bounded_support := ⟨2 * ((n : ℝ) + 1), fun τ y hy => by
    simp [mulT, cutχ_eq_zero n hy.le]⟩

end IsPhaseSchwartz

/-! ### Null sequences of test elements -/

section Null

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

theorem IsSliceTest.neg {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G) :
    IsSliceTest P r (-G) := by
  have h : -G = (-1 : ℂ) • G := by
    funext p
    simp
  rw [h]
  exact hG.const_smul _

theorem testElem_zero : testElem P r 0 = 0 := by
  have h := testElem_const_smul ((IsPhaseTest.zero (P := P)).isSliceTest r) (0 : ℂ)
  simpa using h

theorem testElem_neg {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G) :
    testElem P r (-G) = -testElem P r G := by
  have h : -G = (-1 : ℂ) • G := by
    funext p
    simp
  rw [h, testElem_const_smul hG]
  simp

theorem testElem_real_smul {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G) (c : ℝ) :
    testElem P r (c • G) = (c : ℂ) • testElem P r G := by
  have h : c • G = (c : ℂ) • G := by
    funext p
    simp [Pi.smul_apply, Complex.coe_smul]
  rw [h, testElem_const_smul hG]

/-- A sequence of slice tests whose test elements tend to zero in `Y_r`. -/
structure NullSeq (P : ℝ) [Fact (0 < P)] (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (E : ℕ → ℝ × Space → CVec3) : Prop where
  slice : ∀ n, IsSliceTest P r (E n)
  tendsto : Tendsto (fun n => testElem P r (E n)) atTop (𝓝 0)

theorem NullSeq.mulT (hr : r ≠ ⊤) {m : ℕ → Space → ℝ} (hm : GoodMult m)
    {H : ℝ × Space → CVec3} (hH : IsSliceTest P r H) :
    NullSeq P r (fun n => PhaseSpace.mulT (m n) H) := by
  obtain ⟨L, hL⟩ := hm.bound
  exact ⟨fun n => hH.mulT (hm.cont n) (hL n), tendsto_testElem_mulT hr hH hm.cont hL hm.lim⟩

theorem NullSeq.add {E₁ E₂ : ℕ → ℝ × Space → CVec3} (h₁ : NullSeq P r E₁)
    (h₂ : NullSeq P r E₂) : NullSeq P r (fun n => E₁ n + E₂ n) := by
  refine ⟨fun n => (h₁.slice n).add (h₂.slice n), ?_⟩
  have h : (fun n => testElem P r (E₁ n + E₂ n)) =
      fun n => testElem P r (E₁ n) + testElem P r (E₂ n) :=
    funext fun n => testElem_add (h₁.slice n) (h₂.slice n)
  rw [h]
  simpa using h₁.tendsto.add h₂.tendsto

theorem NullSeq.zero : NullSeq P r (fun _ => 0) :=
  ⟨fun _ => (IsPhaseTest.zero (P := P)).isSliceTest r, by simpa [testElem_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Yq P r)) atTop (𝓝 0))⟩

theorem NullSeq.sum {ι : Type*} (s : Finset ι) {E : ι → ℕ → ℝ × Space → CVec3}
    (h : ∀ i ∈ s, NullSeq P r (E i)) : NullSeq P r (fun n => ∑ i ∈ s, E i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (NullSeq.zero : NullSeq P r (fun _ => 0))
  | insert a s ha ih =>
    have h' := (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h'

theorem tendsto_testElem_of_null {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G)
    {E : ℕ → ℝ × Space → CVec3} (hE : NullSeq P r E) {F : ℕ → ℝ × Space → CVec3}
    (hF : ∀ n, F n = G + E n) :
    Tendsto (fun n => testElem P r (F n)) atTop (𝓝 (testElem P r G)) := by
  have h : (fun n => testElem P r (F n)) = fun n => testElem P r G + testElem P r (E n) :=
    funext fun n => by rw [hF n, testElem_add hG (hE.slice n)]
  rw [h]
  simpa using (tendsto_const_nhds (x := testElem P r G)).add hE.tendsto

end Null

/-! ### Convergence of the cutoff approximants -/

section Approx

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {Ψ : ℝ × Space → CVec3}

theorem cut_decomp (hΨ : IsPhaseSchwartz P r Ψ) (n : ℕ) :
    mulT (cutχ n) Ψ = Ψ + mulT (fun y => cutχ n y - 1) Ψ := by
  funext p
  simp only [mulT, Pi.add_apply]
  module

theorem dy_cut_decomp (hΨ : IsPhaseSchwartz P r Ψ) (j : Fin 3) (n : ℕ) :
    -dy j (mulT (cutχ n) Ψ) =
      -dy j Ψ + (mulT (fun y => cutχ n y - 1) (-dy j Ψ) +
        mulT (fun y => 1 * sd j (cutχ n) y) (-Ψ)) := by
  rw [dy_mulT ((contDiff_cutχ n).differentiable (by simp)) (hΨ.smooth.differentiable (by simp))]
  funext p
  simp only [mulT, Pi.add_apply, Pi.neg_apply]
  module

theorem lapT_cut_decomp (hΨ : IsPhaseSchwartz P r Ψ) (n : ℕ) :
    lapT (mulT (cutχ n) Ψ) =
      lapT Ψ + (mulT (fun y => cutχ n y - 1) (lapT Ψ) +
        (∑ j : Fin 3, mulT (fun y => 2 * sd j (cutχ n) y) (dy j Ψ) +
          mulT (fun y => lapS (cutχ n) y) Ψ)) := by
  funext p
  rw [lapT_mulT_apply (contDiff_cutχ n) hΨ.smooth p]
  simp only [mulT, Pi.add_apply, Finset.sum_apply]
  module

theorem driftT_cut_decomp (hΨ : IsPhaseSchwartz P r Ψ) (n : ℕ) :
    driftT (mulT (cutχ n) Ψ) =
      driftT Ψ + (mulT (fun y => cutχ n y - 1) (driftT Ψ) +
        mulT (fun y => (1 / 2 : ℝ) * radS (cutχ n) y) Ψ) := by
  funext p
  rw [driftT_mulT_apply (contDiff_cutχ n) hΨ.smooth p]
  simp only [mulT, Pi.add_apply]
  module

variable (hr : r ≠ ⊤)
include hr

theorem tendsto_cut (hΨ : IsPhaseSchwartz P r Ψ) :
    Tendsto (fun n => testElem P r (mulT (cutχ n) Ψ)) atTop (𝓝 (testElem P r Ψ)) :=
  tendsto_testElem_of_null hΨ.sliceTest (NullSeq.mulT hr goodMult_cutχ_sub_one hΨ.sliceTest)
    (cut_decomp hΨ)

theorem tendsto_cut_dy (hΨ : IsPhaseSchwartz P r Ψ) (j : Fin 3) :
    Tendsto (fun n => testElem P r (-dy j (mulT (cutχ n) Ψ))) atTop
      (𝓝 (testElem P r (-dy j Ψ))) :=
  tendsto_testElem_of_null (hΨ.sliceTest_dy j).neg
    ((NullSeq.mulT hr goodMult_cutχ_sub_one (hΨ.sliceTest_dy j).neg).add
      (NullSeq.mulT hr (goodMult_sd_cutχ j 1) hΨ.sliceTest.neg))
    (dy_cut_decomp hΨ j)

theorem tendsto_cut_lapT (hΨ : IsPhaseSchwartz P r Ψ) :
    Tendsto (fun n => testElem P r (lapT (mulT (cutχ n) Ψ))) atTop
      (𝓝 (testElem P r (lapT Ψ))) :=
  tendsto_testElem_of_null hΨ.sliceTest_lapT
    ((NullSeq.mulT hr goodMult_cutχ_sub_one hΨ.sliceTest_lapT).add
      ((NullSeq.sum Finset.univ fun j _ =>
          NullSeq.mulT hr (goodMult_sd_cutχ j 2) (hΨ.sliceTest_dy j)).add
        (NullSeq.mulT hr goodMult_lapS_cutχ hΨ.sliceTest)))
    (lapT_cut_decomp hΨ)

theorem tendsto_cut_driftT (hΨ : IsPhaseSchwartz P r Ψ) :
    Tendsto (fun n => testElem P r (driftT (mulT (cutχ n) Ψ))) atTop
      (𝓝 (testElem P r (driftT Ψ))) :=
  tendsto_testElem_of_null hΨ.sliceTest_driftT
    ((NullSeq.mulT hr goodMult_cutχ_sub_one hΨ.sliceTest_driftT).add
      (NullSeq.mulT hr goodMult_radS_cutχ hΨ.sliceTest))
    (driftT_cut_decomp hΨ)

end Approx

/-! ### The extension theorems -/

section Extend

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem conjExp_ne_top (hq : 1 < q) : conjExp q ≠ ⊤ := by
  unfold conjExp
  rw [Ne, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le]
  exact ENNReal.inv_lt_one.2 hq

/-- Passing a tested identity to the limit along approximating tests. -/
theorem HasPhaseOp.extend_of_tendsto {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3}
    {f g : Yq P q} (h : HasPhaseOp Lt f g) {Ψ : ℝ × Space → CVec3}
    {Φ : ℕ → ℝ × Space → CVec3} (hΦ : ∀ n, IsPhaseTest P (Φ n))
    (h₁ : Tendsto (fun n => testElem P (conjExp q) (Φ n)) atTop
      (𝓝 (testElem P (conjExp q) Ψ)))
    (h₂ : Tendsto (fun n => testElem P (conjExp q) (Lt (Φ n))) atTop
      (𝓝 (testElem P (conjExp q) (Lt Ψ)))) :
    phasePair P q (Lt Ψ) f = phasePair P q Ψ g := by
  have c₁ : Tendsto (fun n => phasePair P q (Lt (Φ n)) f) atTop
      (𝓝 (phasePair P q (Lt Ψ) f)) :=
    (((phasePairing P q).flip f).continuous.tendsto _).comp h₂
  have c₂ : Tendsto (fun n => phasePair P q (Φ n) g) atTop (𝓝 (phasePair P q Ψ g)) :=
    (((phasePairing P q).flip g).continuous.tendsto _).comp h₁
  have heq : (fun n => phasePair P q (Lt (Φ n)) f) = fun n => phasePair P q (Φ n) g :=
    funext fun n => h (Φ n) (hΦ n)
  rw [heq] at c₁
  exact tendsto_nhds_unique c₁ c₂

/-- **T25.3 for `∂ⱼ`**: if `∂ⱼ f = g` in distributions, then `⟪-∂ⱼΨ, f⟫ = ⟪Ψ, g⟫` for every
Schwartz-type phase test `Ψ` (`1 < q`). -/
theorem HasPhaseOp.extend_dy (hq : 1 < q) (j : Fin 3) {f g : Yq P q}
    (h : HasPhaseOp (fun Φ => -dy j Φ) f g) {Ψ : ℝ × Space → CVec3}
    (hΨ : IsPhaseSchwartz P (conjExp q) Ψ) :
    phasePair P q (-dy j Ψ) f = phasePair P q Ψ g :=
  h.extend_of_tendsto (Lt := fun Φ => -dy j Φ) hΨ.isPhaseTest_cut
    (tendsto_cut (conjExp_ne_top hq) hΨ) (tendsto_cut_dy (conjExp_ne_top hq) hΨ j)

/-- **T25.3 for `νΔ`**: if `νΔ f = a` in distributions, then `⟪νΔΨ, f⟫ = ⟪Ψ, a⟫` for every
Schwartz-type phase test `Ψ` (`1 < q`). -/
theorem HasPhaseOp.extend_lap (hq : 1 < q) (ν : ℝ) {f a : Yq P q}
    (h : HasPhaseOp (nuLapT ν) f a) {Ψ : ℝ × Space → CVec3}
    (hΨ : IsPhaseSchwartz P (conjExp q) Ψ) :
    phasePair P q (nuLapT ν Ψ) f = phasePair P q Ψ a := by
  refine h.extend_of_tendsto hΨ.isPhaseTest_cut (tendsto_cut (conjExp_ne_top hq) hΨ) ?_
  have h1 : ∀ n, testElem P (conjExp q) (nuLapT ν (mulT (cutχ n) Ψ)) =
      (ν : ℂ) • testElem P (conjExp q) (lapT (mulT (cutχ n) Ψ)) := fun n =>
    testElem_real_smul ((hΨ.isPhaseTest_cut n).lapT.isSliceTest _) ν
  have h2 : testElem P (conjExp q) (nuLapT ν Ψ) =
      (ν : ℂ) • testElem P (conjExp q) (lapT Ψ) :=
    testElem_real_smul hΨ.sliceTest_lapT ν
  simp only [h1, h2]
  exact (tendsto_cut_lapT (conjExp_ne_top hq) hΨ).const_smul _

/-- **T25.3 for `T₀`**: if `T₀ f = b` in distributions, then `⟪T₀ᵗΨ, f⟫ = ⟪Ψ, b⟫` for every
Schwartz-type phase test `Ψ` (`1 < q`). -/
theorem HasPhaseOp.extend_drift (hq : 1 < q) {f b : Yq P q} (h : HasPhaseOp driftT f b)
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseSchwartz P (conjExp q) Ψ) :
    phasePair P q (driftT Ψ) f = phasePair P q Ψ b :=
  h.extend_of_tendsto hΨ.isPhaseTest_cut (tendsto_cut (conjExp_ne_top hq) hΨ)
    (tendsto_cut_driftT (conjExp_ne_top hq) hΨ)

/-- **T25.3 on the free graph** (B0411): for `(w, a, b) ∈ D_(ν,q)` with `1 < q`, both graph
identities hold against every Schwartz-type phase test. -/
theorem freeGraph_extend (hq : 1 < q) {ν : ℝ} {w a b : Yq P q}
    (hw : (w, a, b) ∈ freeGraph P ν q) {Ψ : ℝ × Space → CVec3}
    (hΨ : IsPhaseSchwartz P (conjExp q) Ψ) :
    phasePair P q (nuLapT ν Ψ) w = phasePair P q Ψ a ∧
      phasePair P q (driftT Ψ) w = phasePair P q Ψ b :=
  ⟨hw.1.extend_lap hq ν hΨ, hw.2.extend_drift hq hΨ⟩

end Extend

end UnforcedLeray.PhaseSpace
