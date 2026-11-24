import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04

/-!
# Part II-a, task `PartII-a:F04/1` (decomposition): one global window Laplacian

Source of record: `the November 2 reference manuscript`, lines 1470-1480
(averaging/gluing of the window Laplacians of `LocalWindowEstimate`).

The window Laplacians `Λ_k` (centres `k ∈ ℤ`, windows `|τ - k| < 1`) are glued as follows.

* `WindowLapAEMeas`, `WindowLapLocInt`, `WindowRhsFinite`: each `Λ_k` is a.e. strongly measurable
  and locally integrable on its window (the right side of the window bound is finite).
* `WindowLapUnique`: two window Laplacians of the same `W` agree a.e. on a common open time
  interval (fundamental lemma of the calculus of variations).
* `WindowLapGlue`: a.e.-compatible a.e.-measurable fields on the windows `|τ - k| < 1` glue to one
  strongly measurable field.
* `WindowLapPoU`: a field equal a.e. to a window Laplacian on each integer window is a window
  Laplacian on every window (partition of unity in `τ`; `lapT` commutes with multiplication by a
  function of `τ`).
* `WindowLapPeriodic`: periodicity a.e. by uniqueness applied to the shifted field.

The `L^r` bound on a period is proved in `globalLaplacianField_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep

/-- The window `|τ - τ₀| < 1` times `ℝ³`. -/
def winSet (τ₀ : ℝ) : Set (ℝ × Space) := Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)

/-- **Sub A (measurability; lines 1470-1480).** A window Laplacian is a.e. strongly measurable on
its window. Proof: test with `ψ = φ • e_c` for bumps `φ` covering the window by countably many
balls; `Λ_c φ` is then integrable, hence a.e. strongly measurable on `{φ ≠ 0}`. -/
def WindowLapAEMeas : Prop :=
  ∀ (ν τ₀ : ℝ) (W Λ : ℝ × Space → CVec3), IsWindowLaplacian ν τ₀ W Λ →
    AEStronglyMeasurable Λ (volume.restrict (winSet τ₀))

/-- **Sub B (local integrability).** An a.e. strongly measurable field with finite
`∫⁻_{a<τ<b} ∫⁻ ‖Λ‖^r` (`1 ≤ r < ∞`) is locally integrable on `(a,b) × ℝ³` (compact sets have
finite measure; Hölder/`MemLp.integrableOn`). -/
def WindowLapLocInt : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (a b : ℝ) (Λ : ℝ × Space → CVec3),
    AEStronglyMeasurable Λ (volume.restrict (Ioo a b ×ˢ (univ : Set Space))) →
    ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ →
      LocallyIntegrableOn Λ (Ioo a b ×ˢ (univ : Set Space))

/-- **Sub C (finite right side of the window bound).** For `w, f ∈ Y_r`, `r < ∞`, the right side
of the window estimate is finite (`F03Rep.lintegral_window_lt_top` for `f` and `w` on
`Icc (τ₀-2) (τ₀+2)`; `τ ↦ ‖w τ‖ₑ^r` is a.e. measurable, e.g. from `exists_isRep` and
`Measurable.lintegral_prod_right'`, or use `wn_window_lt_top` of `Tasks/F03bWindowNorms.lean`). -/
def WindowRhsFinite : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ) (f w : Yq P r) (τ₀ : ℝ),
    ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
      (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) < ⊤

/-- **Sub D (uniqueness of the weak Laplacian on an interval).** If `Λ` and `Λ'` are window
Laplacians of the same `W` for centres `τ₀`, `τ₁`, both locally integrable on `(a,b) × ℝ³`, and
`(a,b)` lies in both windows, they agree a.e. on `(a,b) × ℝ³`. Proof: the difference `D` satisfies
`∫ D · ψ = 0` for all smooth compactly supported `ψ` supported in the open set `(a,b) × ℝ³`;
apply `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` componentwise (`ψ = φ e_c`). -/
def WindowLapUnique : Prop :=
  ∀ (ν τ₀ τ₁ a b : ℝ) (W Λ Λ' : ℝ × Space → CVec3),
    τ₀ - 1 ≤ a → b ≤ τ₀ + 1 → τ₁ - 1 ≤ a → b ≤ τ₁ + 1 →
    IsWindowLaplacian ν τ₀ W Λ → IsWindowLaplacian ν τ₁ W Λ' →
    LocallyIntegrableOn Λ (Ioo a b ×ˢ (univ : Set Space)) →
    LocallyIntegrableOn Λ' (Ioo a b ×ˢ (univ : Set Space)) →
      Λ =ᵐ[volume.restrict (Ioo a b ×ˢ (univ : Set Space))] Λ'

/-- **Sub E (gluing).** Fields `Λ_k` (`k ∈ ℤ`), a.e. strongly measurable on `winSet k` and a.e.
equal on overlaps of windows, are the restrictions of one strongly measurable field `Λ`: a.e. on
each `winSet k`, `Λ = Λ_k`. Proof: `g_k` strongly measurable representatives,
`Λ p = g_{⌊p.1⌋} p`; on `winSet k`, `⌊τ⌋ ∈ {k-1, k}` and `g_{k-1} = g_k` a.e. on the overlap. -/
def WindowLapGlue : Prop :=
  ∀ Λk : ℤ → ℝ × Space → CVec3,
    (∀ k : ℤ, AEStronglyMeasurable (Λk k) (volume.restrict (winSet (k : ℝ)))) →
    (∀ k l : ℤ, Λk k =ᵐ[volume.restrict (winSet (k : ℝ) ∩ winSet (l : ℝ))] Λk l) →
      ∃ Λ : ℝ × Space → CVec3, StronglyMeasurable Λ ∧
        ∀ k : ℤ, Λ =ᵐ[volume.restrict (winSet (k : ℝ))] Λk k

/-- **Sub F (partition of unity in `τ`; lines 1475-1478).** If `Λ_k` is a window Laplacian of `W`
for centre `k ∈ ℤ` and `Λ = Λ_k` a.e. on `winSet k` for every `k`, then `Λ` is a window Laplacian
of `W` for every real centre `τ₀`. Proof: a smooth compactly supported `ψ` with
`tsupport ψ ⊆ winSet τ₀` is `∑ₖ χ_k ψ` (finite sum, `χ_k` a smooth partition of unity on `ℝ`
subordinate to `(k-1,k+1)`, `SmoothPartitionOfUnity.exists_isSubordinate`), `lapT (χ_k ψ) =
χ_k lapT ψ` since `χ_k` depends on `τ` only; apply `IsWindowLaplacian` for `Λ_k` to each
`χ_k ψ` and sum (integrals of finite sums, a.e. replacement of `Λ_k` by `Λ`). -/
def WindowLapPoU : Prop :=
  ∀ (ν : ℝ) (W Λ : ℝ × Space → CVec3) (Λk : ℤ → ℝ × Space → CVec3),
    (∀ k : ℤ, IsWindowLaplacian ν (k : ℝ) W (Λk k)) →
    (∀ k : ℤ, Λ =ᵐ[volume.restrict (winSet (k : ℝ))] Λk k) →
      ∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ

/-- **Sub G (periodicity).** If `W` and `Λ` are strongly measurable, `W` is a.e. `P`-periodic in
`τ`, `Λ` is a window Laplacian of `W` for every centre and locally integrable on each integer
window, then `Λ` is a.e. `P`-periodic in `τ`. Proof: `Λ' = Λ(· + P, ·)` is a window Laplacian of
`W(· + P, ·) = W` a.e. for every centre (translation of test functions, `lapT` commutes with
translations), so `Λ' = Λ` a.e. on every window by Sub D, hence a.e. on `ℝ × ℝ³`
(countably many windows); conclude with `Measure.ae_ae_of_ae_prod`. -/
def WindowLapPeriodic : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ (W Λ : ℝ × Space → CVec3), StronglyMeasurable W → StronglyMeasurable Λ →
    (∀ᵐ τ : ℝ, (fun y => W (τ + P, y)) =ᵐ[volume] fun y => W (τ, y)) →
    (∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ) →
    (∀ k : ℤ, LocallyIntegrableOn Λ (winSet (k : ℝ))) →
      ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)

/-- Reduction of `GlobalLaplacianField` to Subs A-G. -/
theorem globalLaplacianField_of (hAE : WindowLapAEMeas) (hLI : WindowLapLocInt)
    (hRHS : WindowRhsFinite) (hUn : WindowLapUnique) (hGl : WindowLapGlue) (hPoU : WindowLapPoU)
    (hPer : WindowLapPeriodic) : GlobalLaplacianField := by
  intro hloc r _ hr1 hrt P _ hP1 ν hν μ f w hf W hW
  obtain ⟨C, hC0, hC⟩ := hloc r hr1 hrt
  have hCP := hC P hP1 ν hν μ f w hf W hW
  choose Λk hΛk hbd using fun k : ℤ => hCP (k : ℝ)
  have hfin2 : ∀ k : ℤ, ∫⁻ τ in Ioo ((k : ℝ) - 1) ((k : ℝ) + 1), ∫⁻ y, ‖Λk k (τ, y)‖ₑ ^ r.toReal
      < ⊤ := by
    intro k
    refine lt_of_le_of_lt (hbd k) (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (hRHS r hrt P μ f w (k : ℝ)))
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable (Λk k) (volume.restrict (winSet (k : ℝ))) :=
    fun k => hAE ν (k : ℝ) W (Λk k) (hΛk k)
  have hli : ∀ k : ℤ, LocallyIntegrableOn (Λk k) (winSet (k : ℝ)) :=
    fun k => hLI r hrt _ _ (Λk k) (hmeas k) (hfin2 k)
  have hover : ∀ k l : ℤ, Λk k =ᵐ[volume.restrict (winSet (k : ℝ) ∩ winSet (l : ℝ))] Λk l := by
    intro k l
    have hset : winSet (k : ℝ) ∩ winSet (l : ℝ) =
        Ioo (max ((k : ℝ) - 1) ((l : ℝ) - 1)) (min ((k : ℝ) + 1) ((l : ℝ) + 1)) ×ˢ
          (univ : Set Space) := by
      unfold winSet
      rw [Set.prod_inter_prod, Set.inter_univ, Set.Ioo_inter_Ioo]
    rw [hset]
    exact hUn ν k l _ _ W (Λk k) (Λk l) (le_max_left _ _) (min_le_left _ _)
      (le_max_right _ _) (min_le_right _ _) (hΛk k) (hΛk l)
      ((hli k).mono_set (by rw [← hset]; exact Set.inter_subset_left))
      ((hli l).mono_set (by rw [← hset]; exact Set.inter_subset_right))
  obtain ⟨Λ, hΛm, hΛeq⟩ := hGl Λk hmeas hover
  have hwin : ∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ :=
    hPoU ν W Λ Λk hΛk hΛeq
  have hWper : ∀ᵐ τ : ℝ, (fun y => W (τ + P, y)) =ᵐ[volume] fun y => W (τ, y) := by
    filter_upwards [hW.slice, hW.slice_shift P] with t h1 h2
    have e : ((P + t : ℝ) : AddCircle P) = (t : AddCircle P) := by
      rw [add_comm]; exact AddCircle.coe_add_period P t
    rw [e] at h2
    rw [add_comm t P]
    exact h2.trans h1.symm
  refine ⟨Λ, hΛm, hwin, ?_, ?_⟩
  · exact hPer P ν (Fact.out) W Λ hW.meas hΛm hWper hwin
      (fun k => (hli k).congr (hΛeq k).symm)
  · -- the `L^r` bound on one period
    have hae : ∀ᵐ τ ∂(volume.restrict (Ioo ((0 : ℤ) - 1 : ℝ) ((0 : ℤ) + 1 : ℝ))),
        ∀ᵐ y, Λ (τ, y) = Λk 0 (τ, y) := by
      have h0 := hΛeq 0
      unfold winSet at h0
      have h0' : Λ =ᵐ[((volume : Measure ℝ).restrict (Ioo ((0 : ℤ) - 1 : ℝ) ((0 : ℤ) + 1 : ℝ))).prod
          (volume : Measure Space)] Λk 0 := by
        rw [Measure.restrict_prod_eq_prod_univ]; exact h0
      exact Measure.ae_ae_of_ae_prod h0'
    have hcongr : ∫⁻ τ in Ioo (0 : ℝ) P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
        ∫⁻ τ in Ioo ((0 : ℤ) - 1 : ℝ) ((0 : ℤ) + 1 : ℝ), ∫⁻ y, ‖Λk 0 (τ, y)‖ₑ ^ r.toReal := by
      have hsub : Ioo (0 : ℝ) P ⊆ Ioo ((0 : ℤ) - 1 : ℝ) ((0 : ℤ) + 1 : ℝ) := by
        intro t ht
        simp only [Int.cast_zero]
        constructor <;> linarith [ht.1, ht.2]
      calc ∫⁻ τ in Ioo (0 : ℝ) P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal
          ≤ ∫⁻ τ in Ioo ((0 : ℤ) - 1 : ℝ) ((0 : ℤ) + 1 : ℝ), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal :=
            lintegral_mono_set hsub
        _ = _ := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae] with τ hτ
            exact lintegral_congr_ae (by filter_upwards [hτ] with y hy; rw [hy])
    rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
    exact lt_of_le_of_lt hcongr (hfin2 0)

end UnforcedLeray.Short.PartIIa
