import UnforcedLeray.Short.PartIIb.Sub.B1

/-!
# Part II-b, task `PartII-b:B1/1`: `TestElemLimit` (dominated convergence over the phase)

Source of record: `the November 2 reference manuscript`. The statement
`TestElemLimit` is defined in `Short/PartII-b/Sub/B1.lean`; this file proves it with no added
hypotheses.

Proof outline. Let `q = conjExp q0E`, `p = q.toReal > 0`, and let `haar` be the probability Haar
measure on the phase circle `AddCircle P`.
1. `testElem Θ n - testElem Θ' = toLp (circleSlice Θ_n - circleSlice Θ')` (`testElem_of`,
   `map_sub`), so `‖testElem Θ n - testElem Θ'‖ₑ ^ p = ∫⁻ x, ‖…‖ₑ ^ p ∂haar`
   (`lintegral_enorm_rpow_Yq`, `ContinuousMap.coeFn_toLp`).
2. The integrand equals `tlSliceDiffPow Θ_n Θ' x = ‖circleSlice Θ_n x - circleSlice Θ' x‖ₑ ^ p`
   at every point `x` (almost everywhere, from step 1), and at a point `x = ↑τ` this is the
   `L^q`-norm of the slice difference at the phase `τ` (`tl_sliceDiffPow_coe`).
3. Every `x` is `↑τ` for some `τ ∈ Icc 0 P` (`AddCircle.eq_coe_Ico`), so the hypotheses give a
   pointwise limit `0` and the uniform bound `(ofReal C) ^ p` for all `x`.
4. Dominated convergence on the probability space `(AddCircle P, haar)` gives convergence of the
   integrals to `0`; the `p`-th root and `toReal` give `‖testElem Θ n - testElem Θ'‖ → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp

/-- Every point of the phase circle is the class of a representative in `Icc 0 P`. -/
theorem tl_exists_mem_Icc {P : ℝ} [Fact (0 < P)] (x : AddCircle P) :
    ∃ b ∈ Icc (0 : ℝ) P, (b : AddCircle P) = x := by
  obtain ⟨b, hb, hbx⟩ := AddCircle.eq_coe_Ico x
  exact ⟨b, Ico_subset_Icc_self hb, hbx⟩

/-- The `p`-th power (`p = r.toReal`) of the norm of the difference of two slice tests, as a
function on the phase circle. -/
def tlSliceDiffPow {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {Φ Ψ : ℝ × Space → CVec3}
    (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) (x : AddCircle P) : ℝ≥0∞ :=
  ‖circleSlice hΦ x - circleSlice hΨ x‖ₑ ^ r.toReal

/-- The `L^r`-norm of the difference of two slices at the phase `τ`. -/
theorem tl_enorm_circleSlice_sub {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) (τ : ℝ) :
    ‖circleSlice hΦ (τ : AddCircle P) - circleSlice hΨ (τ : AddCircle P)‖ₑ
      = eLpNorm (fun y => Φ (τ, y) - Ψ (τ, y)) r (volume : Measure Space) := by
  rw [circleSlice_coe, circleSlice_coe, Lp.enorm_def]
  unfold sliceMap
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (MemLp.toLp _ (hΦ.2.memLp τ)) (MemLp.toLp _ (hΨ.2.memLp τ)),
    (hΦ.2.memLp τ).coeFn_toLp, (hΨ.2.memLp τ).coeFn_toLp] with y h0 h1 h2
  simp only [Pi.sub_apply] at h0
  rw [h0, h1, h2]

theorem tl_sliceDiffPow_coe {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) (τ : ℝ) :
    tlSliceDiffPow hΦ hΨ (τ : AddCircle P)
      = eLpNorm (fun y => Φ (τ, y) - Ψ (τ, y)) r (volume : Measure Space) ^ r.toReal := by
  unfold tlSliceDiffPow
  rw [tl_enorm_circleSlice_sub]

theorem continuous_tlSliceDiffPow {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) :
    Continuous (tlSliceDiffPow hΦ hΨ) := by
  unfold tlSliceDiffPow
  exact ENNReal.continuous_rpow_const.comp
    (continuous_enorm.comp (circleSlice hΦ - circleSlice hΨ).continuous)

theorem tl_sliceDiffPow_le {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) (C : ℝ)
    (hC : ∀ τ ∈ Icc (0 : ℝ) P,
      eLpNorm (fun y => Φ (τ, y) - Ψ (τ, y)) r (volume : Measure Space) ≤ ENNReal.ofReal C)
    (x : AddCircle P) : tlSliceDiffPow hΦ hΨ x ≤ ENNReal.ofReal C ^ r.toReal := by
  obtain ⟨b, hb, rfl⟩ := tl_exists_mem_Icc x
  rw [tl_sliceDiffPow_coe]
  exact ENNReal.rpow_le_rpow (hC b hb) ENNReal.toReal_nonneg

theorem tl_tendsto_sliceDiffPow {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ : ℕ → ℝ × Space → CVec3} {Ψ : ℝ × Space → CVec3}
    (hΦ : ∀ n, IsSliceTest P r (Φ n)) (hΨ : IsSliceTest P r Ψ) (hr : 0 < r.toReal)
    (hconv : ∀ τ ∈ Icc (0 : ℝ) P, Tendsto (fun n =>
      eLpNorm (fun y => Φ n (τ, y) - Ψ (τ, y)) r (volume : Measure Space)) atTop (𝓝 0))
    (x : AddCircle P) : Tendsto (fun n => tlSliceDiffPow (hΦ n) hΨ x) atTop (𝓝 0) := by
  obtain ⟨b, hb, rfl⟩ := tl_exists_mem_Icc x
  have h1 : Tendsto (fun n =>
      eLpNorm (fun y => Φ n (b, y) - Ψ (b, y)) r (volume : Measure Space) ^ r.toReal)
      atTop (𝓝 ((0 : ℝ≥0∞) ^ r.toReal)) :=
    ((ENNReal.continuous_rpow_const (y := r.toReal)).tendsto 0).comp (hconv b hb)
  rw [ENNReal.zero_rpow_of_pos hr] at h1
  exact Tendsto.congr (fun n => (tl_sliceDiffPow_coe (hΦ n) hΨ b).symm) h1

set_option maxHeartbeats 1000000 in
/-- The difference of the `Y_r` elements of two slice tests is the `toLp` of the difference of
their slice maps on the circle. -/
theorem tl_testElem_sub {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) :
    testElem P r Φ - testElem P r Ψ
      = ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r
          (AddCircle.haarAddCircle (T := P)) ℂ (circleSlice hΦ - circleSlice hΨ) := by
  rw [testElem_of hΦ, testElem_of hΨ, map_sub]

set_option maxHeartbeats 1000000 in
/-- The `r.toReal`-th power of the `Y_r`-norm of the difference is the integral of
`tlSliceDiffPow` over the circle. -/
theorem tl_integral_eq {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrtop : r ≠ ⊤)
    {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ) (hΨ : IsSliceTest P r Ψ) :
    ∫⁻ x, tlSliceDiffPow hΦ hΨ x ∂(AddCircle.haarAddCircle (T := P))
      = ‖testElem P r Φ - testElem P r Ψ‖ₑ ^ r.toReal := by
  rw [← lintegral_enorm_rpow_Yq (testElem P r Φ - testElem P r Ψ) hrtop, tl_testElem_sub hΦ hΨ]
  apply lintegral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := r) (𝕜 := ℂ)
    (AddCircle.haarAddCircle (T := P)) (circleSlice hΦ - circleSlice hΨ)] with x hx
  rw [hx, ContinuousMap.sub_apply]
  rfl

/-- Convergence of the `p`-th power (`p > 0`) of a sequence in `ℝ≥0∞` to `0` gives convergence
of the sequence to `0`. -/
theorem tl_tendsto_of_rpow {f : ℕ → ℝ≥0∞} {p : ℝ} (hp : 0 < p)
    (h : Tendsto (fun n => f n ^ p) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (f n ^ p) ^ p⁻¹) atTop (𝓝 ((0 : ℝ≥0∞) ^ p⁻¹)) :=
    ((ENNReal.continuous_rpow_const (y := p⁻¹)).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (inv_pos.2 hp)] at hinv
  exact Tendsto.congr (fun n => ENNReal.rpow_rpow_inv hp.ne' (f n)) hinv

/-- Convergence of the extended norms to `0` gives convergence of the norms to `0`. -/
theorem tl_tendsto_norm_of_enorm {E : Type*} [SeminormedAddCommGroup E] {g : ℕ → E}
    (h : Tendsto (fun n => ‖g n‖ₑ) atTop (𝓝 0)) : Tendsto (fun n => ‖g n‖) atTop (𝓝 0) := by
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h'
  exact Tendsto.congr (fun n => toReal_enorm _) h'

/-- **Generic form of `TestElemLimit`** (dominated convergence over the phase), for an arbitrary
exponent `r ≠ ⊤` with `1 ≤ r`. Keeping `r` abstract keeps the unifier away from `conjExp q0E`. -/
theorem tl_main {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrtop : r ≠ ⊤)
    (Θ : ℕ → ℝ × Space → CVec3) (Θ' : ℝ × Space → CVec3)
    (hΘ : ∀ n, IsSliceTest P r (Θ n)) (hΘ' : IsSliceTest P r Θ')
    (hpt : ∀ τ ∈ Icc (0 : ℝ) P, Tendsto (fun n =>
      eLpNorm (fun y => Θ n (τ, y) - Θ' (τ, y)) r (volume : Measure Space)) atTop (𝓝 0))
    (hbd : ∃ C : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) P,
      eLpNorm (fun y => Θ n (τ, y) - Θ' (τ, y)) r (volume : Measure Space) ≤ ENNReal.ofReal C) :
    Tendsto (fun n => testElem P r (Θ n)) atTop (𝓝 (testElem P r Θ')) := by
  obtain ⟨C, hC⟩ := hbd
  have hr0 : 0 < r.toReal :=
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne' hrtop
  -- uniform bound and pointwise limit of the integrand, at every point of the circle
  have hbound : ∀ n, ∀ x : AddCircle P,
      tlSliceDiffPow (hΘ n) hΘ' x ≤ ENNReal.ofReal C ^ r.toReal :=
    fun n x => tl_sliceDiffPow_le (hΘ n) hΘ' C (hC n) x
  have hlim : ∀ x : AddCircle P,
      Tendsto (fun n => tlSliceDiffPow (hΘ n) hΘ' x) atTop (𝓝 0) :=
    fun x => tl_tendsto_sliceDiffPow hΘ hΘ' hr0 hpt x
  have hmeas : ∀ n, Measurable (fun x => tlSliceDiffPow (hΘ n) hΘ' x) :=
    fun n => (continuous_tlSliceDiffPow (hΘ n) hΘ').measurable
  -- dominated convergence on the probability space `(AddCircle P, haar)`
  have hfin : ∫⁻ _, ENNReal.ofReal C ^ r.toReal ∂(AddCircle.haarAddCircle (T := P)) ≠ ⊤ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact (ENNReal.rpow_lt_top_of_nonneg hr0.le ENNReal.ofReal_ne_top).ne
  have hdom : Tendsto (fun n =>
      ∫⁻ x, tlSliceDiffPow (hΘ n) hΘ' x ∂(AddCircle.haarAddCircle (T := P)))
      atTop (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂(AddCircle.haarAddCircle (T := P)))) :=
    tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C ^ r.toReal)
      hmeas (fun n => ae_of_all _ (hbound n)) hfin (ae_of_all _ hlim)
  rw [lintegral_zero] at hdom
  -- the integrals are the `r.toReal`-th powers of the norms of the differences
  have hpow : Tendsto (fun n => ‖testElem P r (Θ n) - testElem P r Θ'‖ₑ ^ r.toReal)
      atTop (𝓝 0) :=
    Tendsto.congr (fun n => tl_integral_eq hrtop (hΘ n) hΘ') hdom
  have henorm : Tendsto (fun n => ‖testElem P r (Θ n) - testElem P r Θ'‖ₑ) atTop (𝓝 0) :=
    tl_tendsto_of_rpow hr0 hpow
  exact tendsto_iff_norm_sub_tendsto_zero.2 (tl_tendsto_norm_of_enorm henorm)

/-- **`TestElemLimit`**: dominated convergence over the phase. If slice tests `Θ n` converge to
the slice test `Θ'` in `L^{q₀'}` for every phase `τ ∈ [0, P]`, uniformly bounded in `n` and `τ`,
then `testElem Θ n → testElem Θ'` in `Y_{q₀'}`. -/
theorem testElemLimit : TestElemLimit := by
  intro P _ Θ Θ' hΘ hΘ' hpt hbd
  exact tl_main (conjExp_ne_top one_lt_q0E) Θ Θ' hΘ hΘ' hpt hbd

end UnforcedLeray.Short.IIb
